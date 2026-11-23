"""Read-only proof-lint lane; only exact laptop-free project inputs are cached."""
import argparse, copy, importlib.util, json, os, re, shutil, subprocess, tempfile, time
from hashlib import sha256, file_digest
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO='doublemover/diophantine-z-q'
REF='refs/heads/add-quartic-318-326'
CANARY='docs/ci-hodge-compiled-imports-once/'
CACHE_PREFIX='hodge-private-project-lint-v1-Linux-X64-'
PROJECT_CAP=32*1024**2
CONTROL=b'\n-- Exact GitHub cache invalidation control (not publication source).\n'
HEXDIGEST=re.compile(r'[0-9a-f]{64}$')

def need(condition,message):
    if not condition: raise ValueError(message)

def digest(p):
    with p.open('rb') as f: return file_digest(f,'sha256').hexdigest()

def stable(o):
    return json.dumps(o,sort_keys=True,separators=(',',':')).encode('ascii')

def shas(o): return sha256(stable(o)).hexdigest()

def dump(p,o):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(stable(o)+b'\n')

def read(p):return json.loads(p.read_bytes())

def load_canary():
    contract=read(HERE/'contract.json')
    for f,hashval in contract['immutable_files'].items():
        p=ROOT/f
        need(p.is_file() and p.resolve()==p and digest(p)==hashval,'unapproved producer/lint input: '+f)
    mod=importlib.util.spec_from_file_location('original_cache_canary',ROOT/(CANARY+'run.py'))
    c=importlib.util.module_from_spec(mod);mod.loader.exec_module(c)
    plan=contract['coverage']
    by_name={r['name'] for r in plan['donors']+[plan['target']]}
    roots=sorted({d for row in plan['donors']+[plan['target']] for d in row['imports'] if d not in by_name
                  and d.split('.',1)[0] not in ('Lean','Init','Std')})
    need(len(plan['donors'])==7 and roots==plan['roots'],'supported Hodge source/root coverage mismatch')
    c.check_source(plan)
    return c,plan,contract

def trusted(c):
    env={'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':REPO,'GITHUB_REF':REF,
         'GITHUB_EVENT_NAME':'push','GITHUB_RUN_ATTEMPT':'1','RUNNER_OS':'Linux','RUNNER_ARCH':'X64'}
    need(all(os.getenv(k)==x for k,x in env.items()),'only same-owner trusted branch pushes may use project cache')
    push=read(Path(os.environ['GITHUB_EVENT_PATH']))
    head=c.git(ROOT,'rev-parse','HEAD')
    need(os.getenv('GITHUB_SHA')==head==push['after'] and push['forced'] is False,'not a regular trusted push checkout')
    return head

def keys(h,donors):
    table={}
    for r in donors:
        name=r['name']
        table[name]=shas({'environment':h,'module':name,'source':r['sha256'],
                     'imports':[[d,table.get(d,'immutable-system')] for d in sorted(r['imports'])]})
    return table

def compatibility(plan,core,up,contract):
    need(HEXDIGEST.fullmatch(core) and HEXDIGEST.fullmatch(up),'not content-addressed inputs')
    lineage=[[r[k] for k in ('name','sha256','imports')] for r in plan['donors']]
    return CACHE_PREFIX+shas({'lane':contract['lane'],'recipe_sha256':digest(Path(__file__)),
                             'compiler_locks_flags_checker':core,
                             'official_upstream_content':up,'ordered_project_inputs':lineage})

def mutated(plan):
    q=copy.deepcopy(plan)
    donor=q['donors'][0]
    old=(ROOT/donor['path']).read_bytes()
    need(sha256(old).hexdigest()==donor['sha256'],'control donor preimage changed')
    after=old+CONTROL
    donor['sha256']=sha256(after).hexdigest()
    return q,donor['path'],after

def stat_identity(p):
    s=p.stat()
    need(p.is_file() and p.resolve()==p,'upstream artifact not a regular direct file')
    return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

def prepare(c,plan,contract,lint,args,exe,core,version,head):
    out=args.work
    need(not out.exists(),'prepare in a fresh isolated job directory')
    out.mkdir(parents=True)
    upstream=out/'upstream'; upstream.mkdir()
    start=time.perf_counter()
    receipt=c.pin_upstream(plan,lint,core,upstream)
    elapsed=time.perf_counter()-start
    raw=upstream/'upstream.json'
    meta=read(raw); up=digest(raw)
    need(meta['roots']==plan['roots'] and meta['environment']==core,'sealed exact upstream scope differs')
    fingerprint=compatibility(plan,core,up,contract)
    q,_,_=mutated(plan)
    miss=compatibility(q,core,up,contract)
    need(fingerprint!=miss,'changed-dependency key did not invalidate')
    stamps={p:stat_identity(upstream/p) for p in meta['files']}
    state={'head':head,'compiler':version,'environment':core,'upstream_sha256':up,
           'cache_key':fingerprint,'changed_dependency_key':miss,'acquired':receipt,
           'official_seal_seconds':elapsed,'upstream_file_stamps':stamps}
    dump(out/'fingerprint.json',state)
    print(json.dumps({k:v for k,v in state.items() if k!='upstream_file_stamps'}))
    with open(os.environ['GITHUB_OUTPUT'],'a',encoding='utf8') as f:
        print('key='+fingerprint,'changed_key='+miss,sep='\n',file=f)

def local_inputs(c,plan,contract,lint,args,core,head):
    state=read(args.work/'fingerprint.json')
    up=args.work/'upstream'; raw=up/'upstream.json'
    need(raw.resolve()==raw and digest(raw)==state['upstream_sha256'] and state['head']==head and
         state['environment']==core,'trusted job fingerprint changed')
    data=read(raw)
    need(data['roots']==plan['roots'] and data['environment']==core,'wrong pinned upstream type')
    stamp=state['upstream_file_stamps']
    need(set(stamp)==set(data['files']),'wrong official artifact fingerprint inventory')
    dirs=tuple(up/k for k in data['libraries'])
    found={p.relative_to(up).as_posix() for d in dirs for p in d.rglob('*') if p.is_file()}
    need(found==set(stamp),'upstream inventory drift since secure acquisition')
    need(all(stat_identity(up/k)==q for k,q in stamp.items()),'upstream metadata drift since secure acquisition')
    need(all(sum((lib/(n.replace('.','/')+'.olean')).is_file() for lib in dirs)==1 for n in plan['roots']),
         'required official root absent/ambiguous')
    h=lint.digest(lint.json_bytes([core,state['upstream_sha256']]))
    must=compatibility(plan,core,state['upstream_sha256'],contract)
    need(state['cache_key']==must,'exact project cache fingerprint drift')
    return state,h,dirs,must

def verify_cache(lint,path,expected):
    need(path.is_dir() and path.resolve()==path,'not a regular isolated project cache')
    names={p.name for p in path.iterdir()}
    need(names==set(expected.values()),'one exact project entry per covered module is required')
    sizes={}; total=0
    with tempfile.TemporaryDirectory(prefix='project-cache-sha-verify-') as temp:
        out=Path(temp)
        for n,k in expected.items():
            need(lint.restore(path,k,n,out),'absent verified project dependency: '+n)
            files=read(path/k/'entry.json')['files']
            byte_count=sum((path/k/f).stat().st_size for f in files)+(path/k/'entry.json').stat().st_size
            sizes[n]={'files':files,'bytes':byte_count}; total+=byte_count
            for f in out.iterdir():f.unlink()
            need(total<=PROJECT_CAP,'compiled project-only cache exceeded its 32 MiB hard bound')
    return {'project_cache_bytes':total,'modules':sizes}

def reset_local_cache(path):
    # This is the one transient GitHub Actions cache path, never package cache
    # or repository state. Exact symlinks are unlinked, not followed.
    if path.is_symlink():path.unlink()
    elif path.exists():
        if path.is_dir():shutil.rmtree(path)
        else:path.unlink()

def sample_changed(c,lint,plan,q,path,raw,exe,env,h,libs,cache):
    with tempfile.TemporaryDirectory(prefix='closed-dependency-miss-') as t:
        root=Path(t); clone=root/'cache'
        shutil.copytree(cache,clone)
        source_root=root/'sources'
        for f in [*plan['locks'],*(r['path'] for r in q['donors']+[q['target']])]:
            dst=source_root/f; dst.parent.mkdir(exist_ok=True,parents=True)
            dst.write_bytes(raw if f==path else (ROOT/f).read_bytes())
        old_root=c.ROOT
        c.ROOT=source_root
        try:
            return c.sample(lint,q,q['target'],exe,env,h,libs,clone)
        finally:
            c.ROOT=old_root

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=('targets','prepare','primary','validate'))
    p.add_argument('--work',type=Path)
    p.add_argument('--lean',type=Path)
    p.add_argument('--exact-hit',default='')
    p.add_argument('--changed-hit',default='')
    p.add_argument('--producer-key',default='')
    p.add_argument('--producer-objects-sha',default='')
    a=p.parse_args()
    c,plan,contract=load_canary()
    head=trusted(c)
    if a.mode=='targets':
        print(*plan['roots'],sep='\n');return
    need(a.work and a.work.is_absolute() and a.work.parent.resolve()==Path(os.environ['RUNNER_TEMP']).resolve()
         and a.work.name=='hodge-project-cache-v1','not the dedicated Actions cache work directory')
    lint=c.load_lint(plan)
    env=lint.sanitized_env()
    exe,core,version=lint.verified_compiler(str(a.lean),env)
    if a.mode=='prepare':
        prepare(c,plan,contract,lint,a,exe,core,version,head);return
    start=time.perf_counter()
    state,h,libs,primary=local_inputs(c,plan,contract,lint,a,core,head)
    expected=keys(h,plan['donors'])
    donors=list(expected); target=plan['target']['name']
    cache=a.work/'project-cache'
    use=a.exact_hit=='true'
    verify_seconds=time.perf_counter()-start
    if a.mode=='primary':
        if use:
            verify_cache(lint,cache,expected)
        else:
            reset_local_cache(cache)
        result=c.sample(lint,plan,plan['target'],exe,env,h,libs,cache)
        need(result['elaborated']==([target] if use else [*donors,target]) and
             result['reused']==(donors if use else []),'wrong exact warm or cold path')
        payload=verify_cache(lint,cache,expected)
        dump(a.work/'primary-receipt.json',{'status':'PASS','head':head,'cache_key':primary,'exact_hit':use,
               'scope':'supplemental lint, not a proof gate', 'official_seal_seconds':state['official_seal_seconds'],
                'input_metadata_check_seconds':verify_seconds,'trial':result,**payload})
        with open(os.environ['GITHUB_OUTPUT'],'a',encoding='utf8') as f:
            print('objects_sha='+shas(payload),file=f)
    else:
        need(use and a.changed_hit!='true' and a.producer_key==primary,
             'cold/save/warm chain not proven, or changed dependency returned an exact hit')
        payload=verify_cache(lint,cache,expected)
        need(HEXDIGEST.fullmatch(a.producer_objects_sha) and shas(payload)==a.producer_objects_sha,
             'restored dependency objects do not have the producer manifest digest')
        warm=c.sample(lint,plan,plan['target'],exe,env,h,libs,cache)
        need(warm['elaborated']==[target] and warm['reused']==donors and warm['dependency_lean_seconds']==0,
             'warm job rebuilt a cached donor')
        q,path,raw=mutated(plan)
        changed_keys=keys(h,q['donors'])
        invalidated=[n for n in donors if changed_keys[n]!=expected[n]]
        result=sample_changed(c,lint,plan,q,path,raw,exe,env,h,libs,cache)
        need(invalidated and result['elaborated']==[*invalidated,target] and
             result['reused']==[n for n in donors if n not in invalidated],
             'changed source reused stale transitive project inputs')
        need(verify_cache(lint,cache,expected)==payload,'changed check mutated production project cache')
        dump(a.work/'validation-receipt.json',{'status':'PASS','head':head,'cache_key':primary,
            'exact_warm_hit':True,'producer_objects_sha256':a.producer_objects_sha,
            'changed_dependency_hit':False,'changed_key':state['changed_dependency_key'],
            'changed_modules':invalidated,'warm':warm,'mutated':result,**payload})
    print('HODGE_PROJECT_LINT_CACHE',a.mode,'verified bytes:',payload['project_cache_bytes'])

if __name__=='__main__':main()
