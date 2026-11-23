"""Supplemental native lint cache pilot; does not certify or influence a proof gate."""
from contextlib import contextmanager
from hashlib import sha256
from pathlib import Path
import argparse, json, os, platform, shutil, stat, subprocess, sys, tarfile, tempfile, time, zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKFLOW = '.github/workflows/hodge-compiled-imports-canary.yml'
PLAN = HERE/'plan.json'
MAX_TOTAL = 10 * 1024**3
MAX_PACKED = 2 * 1024**3
WORKFLOW_REF = f'doublemover/diophantine-z-q/{WORKFLOW}@refs/heads/add-quartic-318-326'

def need(v, message):
    if not v:
        raise ValueError(message)

def raw(p):
    return p.read_bytes()

def digest(p):
    with p.open('rb') as f:
        return __import__('hashlib').file_digest(f, 'sha256').hexdigest()

def stable(o):
    return json.dumps(o, sort_keys=True, separators=(',', ':')).encode('ascii')

def put(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(stable(obj) + b'\n')

def git(root, *args):
    env = os.environ | dict(GIT_NO_LAZY_FETCH='1', GIT_NO_REPLACE_OBJECTS='1', GIT_TERMINAL_PROMPT='0')
    return subprocess.check_output(['git','-C',str(root),*args],env=env,timeout=30).decode().strip()

def pinned(p, expected):
    need(p.is_file() and p.resolve() == p and digest(p) == expected, 'unexpected reviewed source: '+str(p))
    return p

def abi_compatible(artifact, client, native):
    # Core data and IR are interpreted by the exact pinned compiler. This
    # protocol rejects native libraries outright; keep libc for provenance.
    pure=('system','machine','compiler')
    return (not native and all(artifact.get(k)==client.get(k) for k in pure)) or (
        native and artifact==client)

def compiled(name):
    return name.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig'))

def load_lint(plan):
    pinned(ROOT/'scripts/check_staged_lean.py',plan['checker_sha256'])
    sys.path.insert(0,str(ROOT/'scripts'))
    import check_staged_lean
    return check_staged_lean

def check_source(plan):
    for row in plan['donors']+[plan['target'],plan['negative']]:
        pinned(ROOT/row['path'],row['sha256'])
    for f, h in plan['locks'].items():
        pinned(ROOT/f,h)
    for f, h in plan['stock_inputs'].items():
        pinned(ROOT/f,h)

def hosted(plan):
    expected = {'GITHUB_REPOSITORY':'doublemover/diophantine-z-q','GITHUB_REF':'refs/heads/add-quartic-318-326',
                'GITHUB_EVENT_NAME':'push','GITHUB_RUN_ATTEMPT':'1','RUNNER_OS':'Linux','RUNNER_ARCH':'X64'}
    need(all(os.getenv(k)==v for k,v in expected.items()),'wrong hosted artifact source')
    ev=json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_bytes())
    head=git(ROOT,'rev-parse','HEAD')
    need(os.environ['GITHUB_SHA']==head==ev.get('after') and ev.get('before')==plan['publication_parent'] and
         ev.get('forced') is False and [x.get('id') for x in ev['commits']]==[head] and
         ev['head_commit']['message']==plan['publication_title'],'not a reviewed singleton nonforce push')
    need(git(ROOT,'rev-list','--parents','-n1',head).split()==[head,plan['publication_parent']] and
         git(ROOT,'rev-parse',plan['publication_parent']+'^{tree}')==plan['source_tree'],
         'unexpected exact source ancestry')
    wf=WORKFLOW_REF
    need(os.getenv('GITHUB_WORKFLOW_REF')==wf and os.getenv('GITHUB_WORKFLOW_SHA')==head,'wrong workflow definition')
    return {'run_id':os.environ['GITHUB_RUN_ID'],'attempt':1,'head':head,
            'tree':git(ROOT,'rev-parse','HEAD^{tree}'),'workflow':wf,'workflow_sha':head,
            'workflow_blob':git(ROOT,'rev-parse','HEAD:'+WORKFLOW),
            'workflow_sha256':digest(ROOT/WORKFLOW)}

def pin_upstream(plan, lint, core, dst):
    source_proof=ROOT/'quartics/quartic-318-326/proof/progress'
    pbase=source_proof/'.lake/packages'
    proof=ROOT/'build/dependency-setup'
    sources=json.loads(raw(proof/'sources.json'))
    acquired=json.loads(raw(proof/'hodge-imports.artifacts.json'))
    deps=json.loads(raw(source_proof/'lake-manifest.json'))['packages']
    desired={d['name']:d['rev'] for d in deps}
    need(sources['status']==acquired['status']=='PASS' and sources['proof_check_run'] is acquired['proof_check_run'] is False and
         sources['identity']==acquired['identity'] and {d['name']:d['rev'] for d in sources['packages']}==desired and
         acquired['attempts'][-1]['label']=='upstream-artifacts' and acquired['attempts'][-1]['exit_code']==0,
         'pinned official dependency acquisition did not succeed')
    maps={}; libraries=[]
    for d in deps:
        package=pbase/d['name']
        need(git(package,'rev-parse','HEAD')==d['rev'] and git(package,'remote','get-url','origin')==d['url'],
            'wrong acquired dependency package source: '+d['name'])
        need(not git(package,'status','--porcelain','--untracked-files=no'),'dirty locked package')
        lib=package/'.lake/build/lib/lean'
        if not lib.is_dir(): continue
        key='libs/'+d['name']
        artifacts=[p for p in lib.rglob('*') if p.is_file() and compiled(p.name) and p.relative_to(lib).parts[0].split('.',1)[0] != 'Cache']
        if not artifacts: continue
        libraries.append(key)
        for p in sorted(artifacts):
            need(p.resolve()==p,'redirected acquired artifact')
            rel=key+'/'+p.relative_to(lib).as_posix()
            q=dst/rel; q.parent.mkdir(parents=True,exist_ok=True)
            try: os.link(p,q)
            except OSError: shutil.copyfile(p,q)
            maps[rel]=digest(q)
    need(maps and sum((dst/n).stat().st_size for n in maps)<=MAX_TOTAL,'unbounded or empty official import closure')
    put(dst/'upstream.json',{'version':1,'environment':core,'roots':plan['roots'],
                             'libraries':libraries,'files':maps})
    return {'sources_sha256':digest(proof/'sources.json'),'acquisition_sha256':digest(proof/'hodge-imports.artifacts.json'),
            'dependency_revisions':desired,'upstream_files':len(maps),
            'upstream_unpacked_bytes':sum((dst/n).stat().st_size for n in maps),
            'official_fetch_attempts':acquired['attempts']}

@contextmanager
def stage(plan, leaf):
    with tempfile.TemporaryDirectory(prefix='actual-hodge-lint-') as d:
        root=Path(d)
        git(root,'init','-q')
        git(root,'config','user.name','Scoped fixture')
        git(root,'config','user.email','fixture@example.invalid')
        git(root,'config','core.autocrlf','false')
        git(root,'config','core.hooksPath',str(root/'no-hooks'))
        for src in [*plan['locks'],*(r['path'] for r in plan['donors'])]:
            q=root/src; q.parent.mkdir(exist_ok=True,parents=True)
            q.write_bytes(raw(ROOT/src))
        git(root,'add','.')
        git(root,'commit','-qm','Exact immutable inputs')
        packet='hodge-import-lint-fixture'
        base='quartics/quartic-318-326/proof/intake/'+packet+'/'
        rows=[*plan['donors'],leaf]
        src=root/(base+leaf['name']+'.lean')
        src.parent.mkdir(exist_ok=True,parents=True)
        src.write_bytes(raw(ROOT/leaf['path']))
        mf=root/(base+'intake.json')
        put(mf,{'order':[r['name'] for r in rows],
                'files':{r['name']+'.lean':{k:r[k] for k in ('sha256','imports')} for r in rows}})
        doc='docs/ci-hodge-fixture/CONTRACT.json'
        put(root/doc,{'rows':{packet:{'manifest_sha256':digest(mf),
                                    'source_paths':{r['name']:r['path'] for r in plan['donors']}}}})
        git(root,'add','.'); yield root

def unpack_verified(path,dst,expect):
    # Authenticate the exact service zip once; validate every extracted member before adding it.
    need(path.stat().st_size<=MAX_PACKED and digest(path)==expect.removeprefix('sha256:'),'authenticated zip digest differs')
    with zipfile.ZipFile(path) as z:
        need(z.namelist()==['hodge-imports.tar.zst'],'unsupported artifact transport members')
        info=z.getinfo('hodge-imports.tar.zst')
        need(info.file_size<=MAX_PACKED and stat.S_IFMT(info.external_attr >> 16) in (0,stat.S_IFREG),
             'nonregular or too large compressed member')
        z.extract(info,dst)
    with subprocess.Popen(['zstd','-q','-dc',str(dst/'hodge-imports.tar.zst')],stdout=subprocess.PIPE) as child:
        with tarfile.open(fileobj=child.stdout,mode='r|') as tar:
            index=tar.next()
            need(index is not None and index.isfile() and index.name=='BUNDLE-MANIFEST.json' and index.size<32*1024**2,
                 'missing/configuration-size bundle manifest')
            manifest=json.load(tar.extractfile(index))
            todo=dict(manifest['members'])
            seen=set(); used=0
            for m in iter(tar.next,None):
                rel=m.name
                allowed=(rel=='PRODUCER-RECEIPT.json' or rel=='upstream/upstream.json' or
                    (rel.startswith(('upstream/libs/','project-cache/')) and
                     (compiled(Path(rel).name) or rel.startswith('project-cache/') and Path(rel).name=='entry.json')))
                need(allowed and m.isfile() and m.name in todo and m.name not in seen and
                     all(x not in ('','.','..') for x in m.name.split('/')),'invalid or duplicate artifact member')
                row=todo[m.name]
                need(m.size==row['size'] and m.size>=0 and used + m.size <= MAX_TOTAL,'artifact member size drift')
                q=dst/m.name; q.parent.mkdir(parents=True,exist_ok=True)
                h=sha256()
                with tar.extractfile(m) as reader, q.open('xb') as f:
                    for chunk in iter(lambda:reader.read(2**20),b''):
                        h.update(chunk); f.write(chunk)
                need(h.hexdigest()==row['sha256'],'artifact member changed: '+m.name)
                q.chmod(0o444); seen.add(m.name); used+=m.size
            need(seen==set(todo),'omitted artifact members')
        while child.stdout.read(2**20):
            pass
        child.stdout.close()
        need(child.wait()==0,'zstd transport extraction failed')
    return manifest

def pack(source,out,provenance):
    members={}
    for p in sorted(source.rglob('*')):
        if not p.is_file(): continue
        need(p.resolve()==p,'redirected staged seal file')
        rel=p.relative_to(source).as_posix()
        need(compiled(p.name) or p.name in ('entry.json','upstream.json','PRODUCER-RECEIPT.json'),'unexpected bundle content')
        members[rel]={'size':p.stat().st_size,'sha256':digest(p)}
    need(sum(r['size'] for r in members.values())<=MAX_TOTAL,'bundle scope exceeds size cap')
    manifest={'protocol':1,'provenance':provenance,'members':members}
    out.mkdir(parents=True,exist_ok=True)
    index=source/'BUNDLE-MANIFEST.json'; put(index,manifest)
    target=out/'hodge-imports.tar.zst'
    with subprocess.Popen(['zstd','-q','-T2','-3','-f','-o',str(target)],stdin=subprocess.PIPE) as child:
        with tarfile.open(fileobj=child.stdin,mode='w|',format=tarfile.PAX_FORMAT) as tar:
            for name in ['BUNDLE-MANIFEST.json',*members]:
                p=source/name
                ti=tarfile.TarInfo(name); ti.size=p.stat().st_size; ti.mode=0o444
                with p.open('rb') as f: tar.addfile(ti,f)
        child.stdin.close()
        need(child.wait()==0,'zstd producer packing failed')
    need(target.stat().st_size<=MAX_PACKED,'bundle exceeds packed cache cap')
    return {'packed_bytes':target.stat().st_size,'packed_sha256':digest(target),'member_count':len(members)}

def sample(lint,plan,leaf,exe,env,identity,libs,cache,negative=False):
    stats=dict(elaborated=[],reused=[],module_cache_seconds=0.,dependency_lean_seconds=0.,target_lean_seconds=0.)
    with stage(plan,leaf) as root:
        begin=time.perf_counter()
        index=lint.Staging(root)
        plans=lint.get_plans(index,[])
        stats['index_seconds']=time.perf_counter()-begin
        if cache: cache.mkdir(exist_ok=True,parents=True)
        try:
            lint.run_plan(exe,plans,env,libs,identity,cache,begin+180,stats)
        except lint.LeanFailure as e:
            if not negative: raise
            diags=[]
            for line in str(e).splitlines()[1:]:
                try: diags.append(json.loads(line))
                except json.JSONDecodeError: continue
            kinds=[v['kind'] for v in diags if v.get('severity')=='error']
            need(kinds==['linter.unusedSectionVars']*2,'negative control did not exclusively reproduce the two hosted lint errors: '+str(kinds))
            stats['diagnostics']=diags
        else:
            need(not negative,'known-red staged bytes did not fail')
        index.unchanged()
        stats['source_sha256']=leaf['sha256']; stats['seconds']=time.perf_counter()-begin
    return stats

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['targets','produce','consume'])
    p.add_argument('--lean',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--artifact-dir',type=Path)
    p.add_argument('--zip-sha')
    p.add_argument('--run')
    p.add_argument('--producer-head')
    p.add_argument('--producer-tree')
    a=p.parse_args()
    plan=json.loads(raw(PLAN)); check_source(plan)
    context=None
    if os.getenv('GITHUB_ACTIONS')=='true': context=hosted(plan)
    if a.mode=='targets':
        need(context is not None,'official acquisition is scoped to the one-shot')
        print(*plan['roots'],sep='\n'); return
    need(a.output is not None and a.output.is_absolute(),'specify isolated absolute output')
    lint=load_lint(plan)
    env=lint.sanitized_env()
    exe, core, version=lint.verified_compiler(str(a.lean) if a.lean else None,env)
    need(platform.system()=='Linux' and platform.machine()=='x86_64','compiled artifact is only for Linux x86_64')
    abi={'system':platform.system(),'machine':platform.machine(),'compiler':version,'libc':list(platform.libc_ver())}
    ancestry={k:plan[k] for k in ('publication_parent','source_tree')}
    donors=[x['name'] for x in plan['donors']]
    target=plan['target']['name']
    if a.mode=='produce':
        need(context is not None,'cannot create an apparently hosted artifact locally')
        with tempfile.TemporaryDirectory(prefix='hodge-compiled-cache-') as tmp:
            base=Path(tmp); upstream=base/'upstream'; upstream.mkdir(); cache=base/'project-cache'
            begin=time.perf_counter()
            upstream_receipts=pin_upstream(plan,lint,core,upstream)
            scan_seconds=time.perf_counter()-begin
            up=digest(upstream/'upstream.json')
            begin=time.perf_counter()
            libs, token=lint.upstream(argparse.Namespace(upstream=str(upstream),upstream_sha=up),core,set(plan['roots']))
            verify_seconds=time.perf_counter()-begin
            h=lint.digest(lint.json_bytes([core,token]))
            trial=sample(lint,plan,plan['target'],exe,env,h,libs,cache)
            need(trial['elaborated']==donors+[target] and not trial['reused'] and len(list(cache.iterdir()))==len(donors),
                 'producer did not freshly elaborate all actual donor sources and the target')
            prov={'native_libraries':False,'independent_proof_gate':False,'context':context,'abi':abi,
                  'plan_sha256':digest(PLAN),'environment':core,'provenance':ancestry,
                  'upstream_sha256':up,'source_hashes':{r['path']:r['sha256'] for r in plan['donors']+[plan['target']]}}
            put(base/'PRODUCER-RECEIPT.json',{'status':'PASS','upstream':upstream_receipts,
                  'upstream_seal_seconds':scan_seconds,'upstream_verification_seconds':verify_seconds,'trial':trial})
            print(json.dumps(pack(base,a.output,prov)))
    else:
        need(a.artifact_dir and a.zip_sha and len(a.zip_sha.removeprefix('sha256:'))==64,'missing authenticated archive digest')
        need(a.run and (context is None or a.run==context['run_id']),'wrong authenticated producing run')
        expected_head=context['head'] if context else a.producer_head
        expected_tree=context['tree'] if context else a.producer_tree
        need(expected_head and expected_tree,'local transport requires authenticated producing commit and tree')
        zips=list(a.artifact_dir.rglob('*.zip'))
        need(len(zips)==1,'need exactly one original artifact zip')
        with tempfile.TemporaryDirectory(prefix='hodge-import-verify-') as tmp:
            base=Path(tmp)
            begin=time.perf_counter()
            m=unpack_verified(zips[0],base,a.zip_sha)
            acquisition_seconds=time.perf_counter()-begin
            v=m['provenance']
            need(m['protocol']==1 and v['native_libraries'] is False and abi_compatible(v['abi'],abi,False)
                 and v['environment']==core and v['plan_sha256']==digest(PLAN) and v['provenance']==ancestry and
                 v['context']['run_id']==a.run and v['context']['attempt']==1 and
                 v['context']['head']==expected_head and v['context']['tree']==expected_tree and
                 v['context']['workflow']==WORKFLOW_REF and v['context']['workflow_sha']==expected_head and
                 v['context']['workflow_sha256']==digest(ROOT/WORKFLOW) and
                 (context is None or v['context']==context),'artifact identity/ABI/head does not match this exact sample')
            need(v['source_hashes']=={r['path']:r['sha256'] for r in plan['donors']+[plan['target']]},
                 'exact artifact source closure differs')
            begin=time.perf_counter()
            libs, token=lint.upstream(argparse.Namespace(upstream=str(base/'upstream'),upstream_sha=v['upstream_sha256']),
                                       core,set(plan['roots']))
            verify_seconds=time.perf_counter()-begin
            # Verify once and reuse these roots in an isolated temporary tree, not a
            # writable user's build directory. Warm sample never elaborates donors.
            h=lint.digest(lint.json_bytes([core,token]))
            cold=sample(lint,plan,plan['target'],exe,env,h,libs,None)
            warm=sample(lint,plan,plan['target'],exe,env,h,libs,base/'project-cache')
            negative=sample(lint,plan,plan['negative'],exe,env,h,libs,base/'project-cache',True)
            need(cold['elaborated']==donors+[target] and not cold['reused'] and
                 warm['elaborated']==[target] and warm['reused']==donors and warm['dependency_lean_seconds']==0 and
                 not negative['elaborated'] and negative['reused']==donors,
                 'unmatched cache behavior or dependency rebuild')
            put(a.output/'MATCHED-RECEIPT.json',{'status':'PASS','producer':v,
                'authenticated_zip_sha256':a.zip_sha,'member_count':len(m['members']),
                'transport_verify_seconds':acquisition_seconds,'upstream_full_validation_seconds':verify_seconds,
                'cold':cold,'warm':warm,'negative':negative})

if __name__=='__main__':
    main()
