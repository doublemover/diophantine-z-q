"""Separate reviewed attachment adapter; unchanged stock compiler executes one selected row."""
import argparse, json, os, re, subprocess, sys
from pathlib import Path
from hashlib import sha256

HERE=Path(__file__).resolve().parent
DOC='docs/ci-backward-repairs-once/'
WORKFLOW='.github/workflows/backward-repairs-once.yml'
MARKER=DOC+'REQUEST.json'
CONTROLLER='scripts/check_standalone_intake.py'
BASE='fb81c9479dfaf5ce59320bb7d1b791128473b680'
BASE_TREE='413e35d16d3aa6f3383858b9b33d7e9c1fed0c6c'
RUNNER_BLOB='240cb0255cf8dd9622f66e8bad09e15259231ecd'
REPOSITORY='doublemover/diophantine-z-q'
REF='refs/heads/add-quartic-318-326'

def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return sha256(p.read_bytes()).hexdigest()
def git(repo,*args):
    env={k:v for k,v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_NO_REPLACE_OBJECTS='1',GIT_NO_LAZY_FETCH='1',GIT_TERMINAL_PROMPT='0')
    return subprocess.check_output(['git','--no-replace-objects','-C',str(repo),*args],env=env,timeout=30)

def entries(diff):
    data=diff.decode().split(chr(0))
    need(data and data.pop()=='' and len(data)%2==0,'invalid changed-file record')
    rows=list(zip(data[::2],data[1::2]))
    need(len(rows)==len(set(rows)),'duplicate Git record')
    return set(rows)

def expected_files(plan):
    return {WORKFLOW,MARKER,DOC+'run.py',DOC+'CONTRACT.json',*plan['payload_sha256']}

def evaluate_event(env,event,parents,tree,changes,marker,plan,head):
    need(all(env.get(k)==v for k,v in {
      'GITHUB_ACTIONS':'true','GITHUB_EVENT_NAME':'push','GITHUB_REF':REF,'GITHUB_REPOSITORY':REPOSITORY,
      'GITHUB_RUN_ATTEMPT':'1','GITHUB_SHA':head,'RUNNER_OS':'Linux','RUNNER_ARCH':'X64','ImageOS':'ubuntu24',
    }.items()),'wrong exact hosted feature push')
    need(re.fullmatch('[0-9a-f]{40}',head) and parents==[head,BASE] and tree==BASE_TREE,'wrong ref/parent/tree')
    need(event.get('after')==head and event.get('before')==BASE and event.get('forced') is False and
         [x.get('id') for x in event.get('commits',[])]==[head],'not a single nonforce push')
    need((event.get('head_commit') or {}).get('message')==plan['title'],'wrong authorization title')
    need(changes=={('A',p) for p in expected_files(plan)},'added/modified unexpected path')
    need(marker=={
      'protocol':1,'mode':plan['mode'],'parent':BASE,'tree':BASE_TREE,'rows':list(plan['rows']),
      'payload_sha256':plan['payload_digest']
    },'wrong reviewed marker or selected rows')

def configure(repo,plan):
    sys.path.insert(0,str(repo/'scripts'))
    import check_standalone_intake as st
    need(st.ROOT==repo,'wrong stock controller root')
    need(git(repo,'rev-parse','HEAD:'+CONTROLLER).decode().strip()==RUNNER_BLOB,'unapproved stock controller object')
    need((repo/CONTROLLER).resolve()==repo/CONTROLLER and (repo/CONTROLLER).read_bytes()==git(repo,'cat-file','blob',RUNNER_BLOB),
         'wrong working controller bytes')
    need(st.FLAGS==('-j1','-M','6144','-Ddebug.skipKernelTC=false','-DwarningAsError=true'),'wrong stock flags')
    # Only this per-job process accepts the reviewed isolated rows. The existing
    # repo file and workflow are neither patched nor run through a false SHA.
    cfgs={}
    for n,cfg0 in plan['rows'].items():
        c=dict(cfg0)
        for key in ('source_roots','artifact_roots'):
            c[key]=tuple(c[key])
        st.profile_contract(c)
        cfgs[n]=c
    st.ALLOWLIST=cfgs
    st.PINNED_ORIGINALS=plan['pinned_originals']
    return st,cfgs

def verify(repo,plan,env):
    repo=repo.resolve()
    need(Path(env['GITHUB_WORKSPACE']).resolve()==repo,'wrong hosted directory')
    head=git(repo,'rev-parse','HEAD').decode().strip()
    parents=git(repo,'rev-list','--parents','-n','1',head).decode().split()
    tree=git(repo,'rev-parse',BASE+'^{tree}').decode().strip()
    changes=entries(git(repo,'diff','--name-status','-z','--no-renames',BASE,head))
    g=json.loads(Path(env['GITHUB_EVENT_PATH']).read_bytes())
    marker=json.loads((repo/MARKER).read_bytes())
    evaluate_event(env,g,parents,tree,changes,marker,plan,head)
    need(sha256(json.dumps(plan['payload_sha256'],sort_keys=True,separators=(',',':')).encode()).hexdigest()==plan['payload_digest'],
         'inconsistent exact payload digest')
    for f in expected_files(plan):
        p=repo/f
        entry=git(repo,'ls-tree',head,'--',f).decode().split()[:3]
        need(entry[:2]==['100644','blob'] and p.resolve()==p and p.is_file() and
             p.read_bytes()==git(repo,'cat-file','blob',entry[2]),'unexpected non-tracked file mode/bytes '+f)
        if f in plan['payload_sha256']:
            need(sha(p)==plan['payload_sha256'][f],'different proof bytes at '+f)
    # The controller object is validated before importing any of its code.
    runner=repo/CONTROLLER
    oid=git(repo,'rev-parse',head+':'+CONTROLLER).decode().strip()
    need(oid==RUNNER_BLOB and runner.resolve()==runner and runner.read_bytes()==git(repo,'cat-file','blob',oid),
         'wrong unchanged stock controller')
    return head

def main(action,packet):
    repo=Path.cwd().resolve()
    need(HERE==repo/DOC.rstrip('/'),'scope adapter must run from exact source')
    plan=json.loads((HERE/'CONTRACT.json').read_bytes())
    head=verify(repo,plan,os.environ)
    st,cfgs=configure(repo,plan)
    need(packet in cfgs,'not a reviewed job')
    config=cfgs[packet]
    if action=='targets':
        c,_=st.hosted_identity(repo,os.environ)
        need(c==head,'checkout moved')
        with st.admitted(repo,head,packet,config):
            print(*config['artifact_roots'],sep='\n')
    else:
        st.check(packet,config)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('action',choices=['targets','check']);p.add_argument('--packet',required=True)
    a=p.parse_args();main(a.action,a.packet)
