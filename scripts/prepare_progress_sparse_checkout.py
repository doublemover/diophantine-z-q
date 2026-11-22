#!/usr/bin/env python3
"""Materialize full selected packet and exact predecessor, not a proof shortcut.

The inventory plan materializes all requested packets (all active packets for
legacy requests). Matrix jobs still materialize one complete packet and its
immediate predecessor. Native validation always sees the same committed bytes.
No Lean, artifact trust, source, import, audit, or resource checks are altered.
"""
import argparse,json,os,re,subprocess
from pathlib import Path
EXPERIMENTS='quartics/quartic-318-326/proof/experiments'
NAME=re.compile(r'[a-z][a-z0-9-]*')
def git(root,*args,input=None):
 return subprocess.check_output(['git','--no-replace-objects','-C',str(root),*args],input=input)
def read_json(root,head,path):
 entry=git(root,'ls-tree',head,'--',path).decode()
 if not entry.startswith('100644 blob '):raise ValueError('Expected ordinary tracked metadata: '+path)
 return json.loads(git(root,'show',head+':'+path))
def materialization_paths(root,packet,head):
 if not isinstance(packet,str) or not NAME.fullmatch(packet):raise ValueError('Invalid literal packet name')
 active=read_json(root,head,EXPERIMENTS+'/packets.json')['active_packets']
 if packet not in active:raise ValueError('Packet is not active at exact source')
 prefix=EXPERIMENTS+'/'+packet
 intake=read_json(root,head,prefix+'/intake.json')
 paths=[prefix]
 if 'revision_classification_schema' in intake:
  if type(intake['revision_classification_schema']) is not int or intake['revision_classification_schema']!=1:raise ValueError('Unsupported revision schema')
  app=read_json(root,head,prefix+'/APPLICATION.json')
  refs=[obj[k] for obj,keys in [(intake,('revision_of','revision_source')),(app,('predecessor','revision_source'))] for k in keys if k in obj]
  if 'INHERITANCE.json' in app.get('bindings',{}):
   inheritance=read_json(root,head,prefix+'/INHERITANCE.json')
   if 'predecessor' in inheritance:refs.append(inheritance['predecessor'])
  if not refs or any(not isinstance(x,str) or not NAME.fullmatch(x) or x==packet for x in refs) or len(set(refs))!=1:raise ValueError('Invalid or conflicting immediate predecessor')
  previous=EXPERIMENTS+'/'+refs[0]
  read_json(root,head,previous+'/intake.json')
  paths.append(previous)
 return paths
def request_materialization_paths(root, validated, head):
 # The caller independently validates the push payload and committed marker.
 active=read_json(root,head,EXPERIMENTS+'/packets.json')['active_packets']
 if not isinstance(active,list) or len(active)>16 or any(not isinstance(n,str) for n in active) or len(set(active))!=len(active):
  raise ValueError('Invalid active experiment matrix')
 names=active if validated['schema']==1 else [row['packet'] for row in validated['shards']]
 paths=[]
 for name in dict.fromkeys(names):
  paths.extend(materialization_paths(root,name,head))
 return list(dict.fromkeys(paths))
def main():
 p=argparse.ArgumentParser(description=__doc__)
 mode=p.add_mutually_exclusive_group(required=True)
 mode.add_argument('--packet')
 mode.add_argument('--from-request',action='store_true')
 p.add_argument('--dry-run',action='store_true')
 a=p.parse_args();root=Path(__file__).resolve().parents[1]
 head=git(root,'rev-parse','HEAD').decode().strip()
 if os.environ.get('GITHUB_SHA',head)!=head:raise ValueError('Checkout does not match execution commit')
 if a.from_request:
  from validate_progress_inventory_request import validate
  event=json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
  paths=request_materialization_paths(root,validate(root,event,os.environ),head)
 else:
  git(root,'diff','--quiet','HEAD','--');git(root,'diff','--cached','--quiet','HEAD','--')
  paths=materialization_paths(root,a.packet,head)
 if not a.dry_run:
  if git(root,'config','--bool','core.sparseCheckout').decode().strip()!='true':raise ValueError('Expected initial sparse checkout')
  if paths:git(root,'sparse-checkout','add','--stdin',input=('\n'.join(paths)+'\n').encode())
  git(root,'diff','--quiet','HEAD','--');git(root,'diff','--cached','--quiet','HEAD','--')
 print(json.dumps({'status':'SPARSE_PATHS_ONLY_NOT_PROOF_ACCEPTANCE','commit':head,'packet':a.packet,'full_directories':paths,'dry_run':a.dry_run},indent=2))
if __name__=='__main__':main()
