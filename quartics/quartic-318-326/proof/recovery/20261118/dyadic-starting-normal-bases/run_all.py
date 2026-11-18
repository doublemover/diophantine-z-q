from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import product
import json,time
from engine import run
here=Path(__file__).resolve().parent;out=here/'records_v2';out.mkdir(exist_ok=True)
def one(job):
 q,ch=job
 p=out/(''.join({1:'p',-1:'m',2:'P',-2:'M'}[i] for i in q)+'-'+ch+'.json')
 r=run(q,ch);p.write_text(json.dumps(r,separators=(',',':'))+'\n')
 return p.name
if __name__=='__main__':
 jobs=list(product(product((1,-1,2,-2),repeat=4),('finite','reciprocal')))
 ts=time.monotonic()
 with ProcessPoolExecutor(max_workers=2) as ex:
  for j,f in enumerate(as_completed([ex.submit(one,v) for v in jobs]),1):
   try:n=f.result()
   except Exception as e:print('ERROR',repr(e),flush=True);continue
   if j%16==0:print(j,n,round(time.monotonic()-ts,2),flush=True)
