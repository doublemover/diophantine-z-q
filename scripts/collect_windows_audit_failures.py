#!/usr/bin/env python3
"""Collect every recorded audit failure, not build artifacts or whole logs. No Lean runs."""
import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import uuid
import zipfile

MARKER = re.compile(r'(?i)(\berror\b|\bfatal\b|traceback|\b\w*(?:Error|Exception)\b|WALL_CLOCK_LIMIT_EXCEEDED|timed?\s*out|\btimeout\b|out of memory|\bkilled\b|\bpanic\b|\bfailed\b|segmentation fault|access violation)')
MAX_JSON = 16 * 1024 * 1024

def collect(run, output, excerpt_chars=32768):
    run = Path(run).resolve()
    output = Path(output).resolve()
    if not run.is_dir():
        raise ValueError('Audit run directory does not exist: ' + str(run))
    if output == run or run in output.parents:
        raise ValueError('Output must be outside the audited run directory')
    output.mkdir(parents=True, exist_ok=False)
    records, problems, inventory, log_paths, metadata = {}, [], [], [], []
    def relative(p):
        return p.relative_to(run).as_posix()
    def add(key, reason, **details):
        row = records.setdefault(key, {'source': key, 'reasons': []})
        if reason not in row['reasons']:
            row['reasons'].append(reason)
        row.update(details)
    def walk_error(exc):
        problems.append({'path': str(exc.filename), 'error': str(exc)})
    for folder, dirs, files in os.walk(run, followlinks=False, onerror=walk_error):
        for name in list(dirs):
            p = Path(folder) / name
            if p.is_symlink():
                dirs.remove(name)
                problems.append({'path': relative(p), 'error': 'Skipped directory symlink'})
        for name in files:
            p = Path(folder) / name
            if p.is_symlink():
                problems.append({'path': relative(p), 'error': 'Skipped file symlink'})
                continue
            if name.lower().endswith('.log'):
                log_paths.append(p)
            if name.lower() in {'summary.json', 'result.json', 'commands.json', 'plan.json'}:
                metadata.append(p)
    # Structured failures remain present even if the corresponding log is absent or empty.
    expected_logs = {}
    def expect(p, reason):
        key = relative(p)
        expected_logs.setdefault(key, []).append(reason)
        add(key, reason)
    for p in sorted(metadata):
        try:
            if p.stat().st_size > MAX_JSON:
                raise ValueError('Metadata exceeds 16 MiB safety bound; not parsed')
            data = json.loads(p.read_text(encoding='utf-8-sig'))
        except (OSError, UnicodeError, ValueError) as exc:
            problems.append({'path': relative(p), 'error': str(exc)})
            add(relative(p), 'Unreadable or invalid metadata')
            continue
        name = p.name.lower()
        if isinstance(data, dict):
            status = data.get('status')
            if status and status != 'PASS':
                add(relative(p), 'Recorded status: ' + str(status), error=str(data.get('error', '')),
                    status=status)
            if name == 'summary.json':
                for label, row in data.get('stages', {}).items():
                    if isinstance(row, dict) and row.get('exit_code') not in (None, 0):
                        expect(p.parent / (label + '.log'), 'Stage exit: ' + str(row['exit_code']))
                for label, code in data.get('packets', {}).items():
                    if code != 0:
                        expect(p.parent / ('packet-' + label + '.log'), 'Packet exit: ' + str(code))
                missing = sorted(set(data.get('active_packets', [])) - set(data.get('packets', {})))
                if missing:
                    add(relative(p), 'Packets without a recorded completion (blocked/running/interrupted)',
                        packets_without_completion=missing)
                if data.get('head'):
                    add_head = data['head']
                else:
                    add_head = None
                inventory.append({'source': relative(p), 'status': status, 'head': add_head,
                                  'stages': data.get('stages', {}), 'packets': data.get('packets', {})})
                if status != 'PASS':
                    ep = p.parent / 'exception.log'
                    if ep.exists():
                        expect(ep, 'Runner exception')
            rows = data.get('commands', [])
        else:
            rows = data if isinstance(data, list) else []
        for row in rows:
            if isinstance(row, dict) and row.get('exit_code') not in (None, 0):
                module = str(row.get('module', 'UNKNOWN'))
                expect(p.parent / 'logs' / (module.replace('/', '_') + '.log'),
                       'Module exit: ' + str(row['exit_code']))
    if not metadata and not log_paths:
        problems.append({'path': str(run), 'error': 'No audit metadata or logs found'})
    by_name = {}
    for p in log_paths:
        by_name.setdefault(p.name, []).append(p)
    # Scan every log, including orphaned/partial logs and infrastructure failures.
    # read bounded fragments even when a log has a huge single line.
    for p in sorted(log_paths):
        key = relative(p)
        try:
            before = p.stat()
            digest = hashlib.sha256()
            with p.open('rb') as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(block)
            with p.open('rb') as stream:
                bom = stream.read(4)
            encoding = 'utf-16' if bom[:2] in (b'\xff\xfe', b'\xfe\xff') else 'utf-8-sig'
            first, tail, hits, hit_count, replacements, long_fragments = [], deque(maxlen=20), [], 0, 0, 0
            used, line, after_hit = 0, 1, 0
            context = deque(maxlen=2)
            with p.open('r', encoding=encoding, errors='replace', newline='') as stream:
                carry = ''
                while True:
                    fragment = stream.readline(65536)
                    if not fragment:
                        break
                    clipped = fragment.rstrip('\r\n')
                    if '\ufffd' in fragment:
                        replacements += 1
                    if len(clipped) > 1000:
                        clipped = clipped[:1000] + ' [line fragment clipped]'
                    entry = {'line': line, 'text': clipped}
                    hit = bool(MARKER.search(carry + fragment))
                    carry = fragment[-80:] if not fragment.endswith('\n') else ''
                    if hit:
                        hit_count += 1
                        if len(hits) < 40:
                            hits.append(line)
                        after_hit = 2
                        candidates = list(context) + [entry]
                    elif after_hit:
                        after_hit -= 1
                        candidates = [entry]
                    else:
                        candidates = []
                    for candidate in candidates:
                        cost = len(candidate['text']) + 32
                        if used + cost <= excerpt_chars // 2 and candidate not in first:
                            first.append(candidate)
                            used += cost
                    tail.append(entry)
                    context.append(entry)
                    # Baseline compile_one can fail before commands.json is written.
                    try:
                        row = json.loads(fragment)
                    except (ValueError, TypeError):
                        row = None
                    if isinstance(row, dict) and row.get('exit_code') not in (None, 0):
                        add(key, 'Nonzero command exit in streamed stage log')
                        stem = str(row.get('module', '')).replace('/', '_') + '.log'
                        if p.parent == run and p.stem.startswith('packet-'):
                            target = run / ('packet-output-' + p.stem[len('packet-'):]) / 'logs' / stem
                            matches = [target] if target in log_paths else []
                        elif p.parent == run and p.stem.startswith('cohort-'):
                            target = run / 'bundles' / ('progress-' + p.stem) / 'logs' / stem
                            matches = [target] if target in log_paths else []
                        else:
                            matches = by_name.get(stem, [])
                        if not matches:
                            add(key, 'Missing referenced module log: ' + stem)
                        for target in matches:
                            add(relative(target), 'Module exit from ' + key + ': ' + str(row['exit_code']))
                    if fragment.endswith('\n'):
                        line += 1
                    else:
                        long_fragments += 1
            if hit_count:
                add(key, 'Diagnostic marker in log (candidate; may be a quoted warning)')
            if key in records:
                remaining, end = excerpt_chars - used, []
                for item in reversed(tail):
                    if item in first:
                        continue
                    cost = len(item['text']) + 32
                    if cost > remaining:
                        continue
                    end.append(item)
                    remaining -= cost
                excerpt = first + list(reversed(end))
                records[key].update(size_bytes=before.st_size, sha256=digest.hexdigest(),
                    diagnostic_fragments=hit_count, first_matching_lines=hits,
                    matching_line_index_truncated=hit_count > len(hits), excerpt=excerpt,
                    excerpt_is_partial=True, encoding=encoding,
                    decoding_replacement_fragments=replacements, long_or_final_line_fragments=long_fragments)
            after = p.stat()
            if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                problems.append({'path': key, 'error': 'Log changed while collecting; rerun after audit stops'})
        except OSError as exc:
            add(key, 'Unreadable log', error=str(exc))
            problems.append({'path': key, 'error': str(exc)})
    present = {relative(p) for p in log_paths}
    for key in expected_logs:
        if key not in present:
            records[key]['missing_log'] = True
            problems.append({'path': key, 'error': 'Referenced failure log is missing'})
    for row in records.values():
        if len(row.get('error', '')) > excerpt_chars:
            row['error_original_characters'] = len(row['error'])
            row['error'] = row['error'][:excerpt_chars] + ' [metadata error clipped]'
    # Logs referenced by later stage logs may already have been scanned. Fill bounded tail for those.
    for key, row in records.items():
        if key in present and 'excerpt' not in row:
            try:
                with (run / key).open('r', encoding='utf-8-sig', errors='replace') as stream:
                    tail = deque(maxlen=8)
                    number = 1
                    while True:
                        chunk = stream.readline(65536)
                        if not chunk:
                            break
                        tail.append({'line': number, 'text': chunk[:500].rstrip()})
                        if chunk.endswith('\n'):
                            number += 1
                row.update(excerpt=list(tail), excerpt_is_partial=True)
            except OSError as exc:
                row['error'] = str(exc)
    # Preserve complete multi-line Lean goals and types for small logs. This final
    # pass also covers silent failures discovered only in a later stage log.
    for key, row in records.items():
        if key not in present:
            continue
        row['full_text_included'] = False
        row['excerpt'] = sorted(row.get('excerpt', []), key=lambda item: item['line'])
        try:
            path = run / key
            before = path.stat()
            if before.st_size > excerpt_chars:
                row['omission_reason'] = 'Log exceeds per-log byte budget; bounded diagnostic context and tail only'
                if 'sha256' not in row:
                    digest = hashlib.sha256()
                    with path.open('rb') as stream:
                        for block in iter(lambda: stream.read(1024 * 1024), b''):
                            digest.update(block)
                    row.update(size_bytes=before.st_size, sha256=digest.hexdigest())
                    after = path.stat()
                    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                        problems.append({'path': key, 'error': 'Log changed during late hash read; rerun after audit stops'})
                continue
            with path.open('rb') as stream:
                raw = stream.read(excerpt_chars + 1)
            after = path.stat()
            if len(raw) > excerpt_chars or (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                problems.append({'path': key, 'error': 'Log changed during full-text read; rerun after audit stops'})
                continue
            encoding = 'utf-16' if raw[:2] in (b'\xff\xfe', b'\xfe\xff') else 'utf-8-sig'
            decoded = raw.decode(encoding, errors='replace')
            row.update(excerpt=[{'line': i, 'text': text} for i, text in enumerate(decoded.splitlines(), 1)],
                       excerpt_is_partial=False, full_text_included=True, encoding=encoding,
                       size_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
            row['full_text_decoding_replacements'] = decoded.count('\ufffd')
        except OSError as exc:
            problems.append({'path': key, 'error': str(exc)})
    result = {'schema': 2, 'audit_root': str(run), 'created_utc': datetime.now(timezone.utc).isoformat(),
        'scope': 'Every recorded structured failure and every marker-bearing log; not failures in blocked/unrun modules.',
        'collector_complete': not problems, 'collection_problems': problems,
        'logs_scanned': len(log_paths), 'metadata_files_scanned': len(metadata),
        'summary_inventory': inventory, 'records': [records[k] for k in sorted(records)],
        'excerpt_character_budget_per_log': excerpt_chars,
        'full_log_byte_budget': excerpt_chars,
        'notice': 'Complete decoded text of logs within the per-log byte budget is included, with line numbers. Larger logs retain bounded diagnostic context and tail; omissions and original paths/hashes are explicit. No failure record count cap. Markers are candidates, not proof of failure. Collection does not run Lean or modify audit logs.'}
    (output / 'failures.json').write_text(json.dumps(result, indent=2, ensure_ascii=True) + '\n', encoding='utf-8')
    with (output / 'failures.txt').open('w', encoding='utf-8') as report:
        report.write(result['scope'] + '\n' + result['notice'] + '\nAudit root: ' + str(run) + '\n')
        report.write(f"Logs scanned: {len(log_paths)}; records: {len(records)}; collection problems: {len(problems)}\n")
        for row in result['records']:
            report.write('\n===== ' + row['source'] + ' =====\n' + '\n'.join(row['reasons']) + '\n')
            if row.get('error'):
                report.write(row['error'] + '\n')
            if row.get('missing_log'):
                report.write('MISSING LOG\n')
            for item in row.get('excerpt', []):
                report.write(str(item['line']) + ': ' + item['text'] + '\n')
            if row.get('excerpt_is_partial'):
                report.write('[Bounded excerpt; consult original file for omitted content.]\n')
            elif row.get('full_text_included'):
                report.write('[Complete decoded log text included.]\n')
        report.write('\nCollection problems: ' + json.dumps(problems, ensure_ascii=True) + '\n')
    archive = output / 'audit-failures.zip'
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as bundle:
        for name in ('failures.json', 'failures.txt'):
            bundle.write(output / name, name)
    return result, archive

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--run', type=Path)
    group.add_argument('--latest', action='store_true')
    parser.add_argument('--audit-root', type=Path, default=Path(__file__).resolve().parents[1] / 'audit-results')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--excerpt-chars', type=int, default=32768)
    args = parser.parse_args()
    if not 1024 <= args.excerpt_chars <= 65536:
        parser.error('--excerpt-chars must be between 1024 and 65536')
    if args.latest:
        runs = [p for p in args.audit_root.glob('windows-*') if p.is_dir() and (p / 'summary.json').is_file()]
        if not runs:
            parser.error('No windows-* run with summary.json found; use --run for a different output directory')
        run = max(runs, key=lambda p: ((p / 'summary.json').stat().st_mtime_ns, p.name))
    else:
        run = args.run
    output = args.output or run.resolve().parent / ('failure-report-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid.uuid4().hex[:8])
    result, archive = collect(run, output, args.excerpt_chars)
    print('Share this compact file:', archive)
    print('Records:', len(result['records']), '| logs scanned:', result['logs_scanned'], '| collector complete:', result['collector_complete'])
    return 0 if result['collector_complete'] else 2

if __name__ == '__main__':
    raise SystemExit(main())
