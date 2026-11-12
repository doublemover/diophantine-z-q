#!/usr/bin/env python3
"""Read-only lexical section-variable candidate audit. NOT Lean elaboration.
Scans exact committed Git blobs, deduplicating copies while retaining all paths.
Never auto-fixes declarations or labels a lexical candidate a confirmed error.
"""
import argparse,collections,hashlib,json,re,subprocess
from pathlib import Path
from check_lean import code_only
TOKEN=re.compile(r"[A-Za-z_\u0080-\uffff][\w'\u0080-\uffff]*")
CMD=re.compile(r'^[ \t]*(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|public|noncomputable|local|scoped)\s+)*(?P<kind>variable|include|omit|section|namespace|end|theorem|lemma|def|abbrev|instance|structure|class|inductive|example|open|universe|set_option|attribute|export|macro|syntax|elab|notation|infixl|infixr|prefix|postfix|initialize)\b',re.M)
def words(s):return set(TOKEN.findall(s))
def binders(s):
 out={};j=0
 while j<len(s):
  if s[j] not in '({[':j+=1;continue
  first=s[j];stack=[first];k=j+1
  while k<len(s) and stack:
   if s[k] in '({[':stack.append(s[k])
   elif s[k] in ')}]':stack.pop()
   k+=1
  group=s[j+1:k-1];j=k
  if first=='[' or ':' not in group:continue
  names,ty=group.split(':',1)
  if ':=' in names or any(c in names for c in '(){}[]'):continue
  for n in TOKEN.findall(names):out[n]=ty
 return out

def split_proof(block):
 # Skip assignments inside binder brackets and target-level let/letI/have.
 # This is lexical only; macros/equation syntax still require explicit review.
 stack=[];pending=0;j=0
 while j<len(block):
  c=block[j]
  if c in '({[':stack.append(c);j+=1;continue
  if c in ')}]':
   if stack:stack.pop()
   j+=1;continue
  if not stack:
   m=TOKEN.match(block,j)
   if m:
    if m.group() in {'let','letI','have','haveI'}:pending+=1
    j=m.end();continue
   if block.startswith(':=',j):
    if pending:pending-=1;j+=2;continue
    return block[:j],block[j+2:]
  j+=1
 return None

def scan(text):
 code=code_only(text);events=list(CMD.finditer(code));env={};inc=set();stack=[];once_add=set();once_remove=set();rows=[];decls=0;uncertain=[]
 for idx,m in enumerate(events):
  end=events[idx+1].start() if idx+1<len(events) else len(code);block=code[m.end():end];kind=m['kind'];line=code.count('\n',0,m.start())+1
  if kind in ['section','namespace']:
   stack.append((dict(env),set(inc)));continue
  if kind=='end':
   if stack:env,inc=stack.pop()
   continue
  if kind=='variable':env.update(binders(block));continue
  if kind in ['include','omit']:
   first=block.splitlines()[0] if block.splitlines() else '';ns=words(first)-{'in'}
   if re.search(r'\bin\b',first):
    (once_add if kind=='include' else once_remove).update(ns)
   elif kind=='include':inc.update(ns)
   else:inc-=ns
   continue
  if kind not in ['theorem','lemma','example']:
   if kind in ['def','abbrev','instance','structure','class','inductive']:once_add.clear();once_remove.clear()
   continue
  decls+=1
  parts=split_proof(block)
  if parts is None:
   uncertain.append({'line':line,'reason':'No := proof separator; equation-style or unsupported declaration'});once_add.clear();once_remove.clear();continue
  sig,body=parts;name_match=TOKEN.search(sig);name=name_match.group() if name_match else '<example>'
  bound=binders(sig);used=words(body);needed=words(sig)|((inc|once_add)-once_remove)
  # Types of signature variables can bring section dependencies automatically.
  changed=True
  while changed:
   old=set(needed)
   for n in needed.copy():
    if n in env:needed|=words(env[n])
   changed=needed!=old
  localnames=set()
  for lm in re.finditer(r'\b(?:have|let|intro|rintro|obtain)\s+([^\n:=]+)',body):localnames|=words(lm.group(1))
  for n in sorted(set(env)&used-needed-set(bound)):
   rows.append({'declaration':name,'line':line,'variable':n,'variable_type':env[n].strip()[:500],'category':'shadowing_possible' if n in localnames else 'proof_only_section_variable_candidate','signature':sig.strip()[:1000]})
  once_add.clear();once_remove.clear()
 return rows,decls,uncertain

def selftest():
 fixtures=[('variable (p : Prop) (hp : p)\nlemma x : p := by exact hp',{'hp'}),('variable (p : Prop) (hp : p)\ninclude hp in\nlemma x : p := by exact hp',set()),('variable (p : Prop) (hp : p)\ninclude hp\nlemma x : p := by exact hp',set()),('variable (p : Prop) (hp : p)\nlemma x (hp : p) : p := by exact hp',set()),('variable (p : Prop) (hp : p)\n/-- hp --/\nlemma x : True := by trivial',set()),('variable (p : Prop) (hp : p)\nsection\ninclude hp\nlemma x : p := by exact hp\nend\nlemma y : p := by exact hp',{'hp'}),('variable (p : Prop) (hp : p)\ndef x : p := hp',set())]
 fixtures += [('variable (p : Prop) (hp : p)\nlemma x : let h := hp; p := by exact h',set()), ('variable (p : Prop) (hp : p)\nlemma x (n : Nat := 0) : p := by exact hp',{'hp'}), ('variable (p : Prop) (hp : p)\nlemma x : letI : Fact p := ⟨hp⟩; p := by exact Fact.out',set())]
 for source,expected in fixtures:assert {x['variable'] for x in scan(source)[0]}==expected
 return len(fixtures)
def main():
 a=argparse.ArgumentParser();a.add_argument('--revision',default='HEAD');a.add_argument('--output',required=True);a.add_argument('--self-test',action='store_true');args=a.parse_args();tests=selftest();head=subprocess.check_output(['git','rev-parse',args.revision],text=True).strip();blobpaths=collections.defaultdict(list)
 for row in subprocess.check_output(['git','ls-tree','-r','-z',head]).split(b'\0'):
  if not row:continue
  meta,path=row.split(b'\t',1);mode,kind,sha=meta.split()
  if kind==b'blob' and path.endswith(b'.lean'):blobpaths[sha.decode()].append(path.decode())
 proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);data,_=proc.communicate(('\n'.join(blobpaths)+'\n').encode());assert proc.returncode==0
 pos=0;results=[];totaldecls=0;unsupported=[]
 for expected,paths in blobpaths.items():
  stop=data.index(b'\n',pos);sha,kind,size=data[pos:stop].split();assert sha.decode()==expected and kind==b'blob';size=int(size);source=data[stop+1:stop+1+size];pos=stop+size+2
  try:rows,decls,unc=scan(source.decode('utf-8'));totaldecls+=decls
  except Exception as ex:unsupported.append({'blob':expected,'paths':paths,'reason':str(ex)});continue
  if rows:results.append({'blob':expected,'sha256':hashlib.sha256(source).hexdigest(),'paths':paths,'candidates':rows})
  if unc:unsupported.append({'blob':expected,'representative':paths[0],'declarations':unc})
 out={'revision':head,'scope':'Every tracked .lean blob in exact branch commit, including archived and third-party copies; not untracked drafts.','tracked_lean_paths':sum(map(len,blobpaths.values())),'unique_lean_blobs':len(blobpaths),'unique_theorem_lemma_example_declarations_seen':totaldecls,'selftests_passed':tests,'candidate_blob_count':len(results),'candidate_count':sum(len(x['candidates']) for x in results),'candidates':results,'unsupported':unsupported,'limits':['Lexical advisory scan, not a Lean parser/typechecker or proof validation.','Only theorem/lemma/example with := and recognized line-leading commands; equation-style declarations are reported unsupported.','No macro expansion, namespace resolution, notation elaboration, typeclass dependency inference or exact lexical-shadow semantics.','Token use may be qualified name or local shadow; categories are candidates requiring source review, not confirmed errors.','Same-line scoped commands such as include hp in lemma ... are not recognized as declarations and may be omitted without an unsupported record.', 'Scoped variable (...) in is not modeled: its binders may leak into subsequent lexical candidates.', 'Qualified names such as Nat.x can match an unrelated section variable x.', 'This scan detects textual proof-only references, not hidden premises in elaborated types; automatic section/typeclass dependency capture requires hosted elaborated-type versus source-syntax inspection.', 'Passed scan cannot certify absence of omitted binders.']};Path(args.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['candidates','unsupported']}));print('unsupported_records',len(unsupported))
if __name__=='__main__':main()
