from math import gcd,prod
import original_probe as i
import json
def primes():
 proof=i.data['primality']
 for p in sorted(map(int,proof)):
  g,f=proof[str(p)]
  if p==2:continue
  assert all(q<p and str(q) in proof and v>0 for q,v in f)
  assert p-1==prod(q**v for q,v in f) and pow(g,p-1,p)==1
  assert all(gcd(pow(g,(p-1)//q,p)-1,p)==1 for q,v in f)
 return set(map(int,proof))
def leg(a,p):
 s=pow(a%p,(p-1)//2,p);assert s
 return 1 if s==1 else -1
def main():
 allp=primes();B=i.beta; bp=[5,11,17,163,661,733,1489,1861];assert B==prod(bp)
 ds={p:i.probe(p) for p in map(int,i.data['annihilators'])}
 assert all(ds.values()) and all(z['D'] for z in ds.values())
 # 7 splits. At +sqrt2=3 reduced smooth cusp, 2h=2m=6 mod7, so 2hR=2mR=-R.
 # Other component good order 8, formal ratio (m/h)^2=1. U_h^2 residues (2,0).
 p=7
 assert i.h%7==i.m%7==3 and (i.m//i.h)%7==1 and i.h%8==0
 N=(1+2*pow(i.r,-1,p))%p;q2=pow(i.r,-30,p);W=(N*N+i.r*q2)%p
 d7=(1-i.A*W**2*pow(17*(1+i.A)**2,-1,p))%p;assert d7==6
 dirs={}
 for k in (4,12,16,48):
  m=B*k*k;r=B*(1-m)*(25*m-9);s=16*B*(1-m)*m
  ds1,ds2=[{int(p):v for p,v in row.items()} for row in i.data['baseline_factors'][str(k)]]
  assert prod(p**v for p,v in ds1.items())==m-1 and prod(p**v for p,v in ds2.items())==25*m-9
  ps=set(ds1)|set(ds2)|set(bp)|{2,3};assert ps<=allp
  out=[];sign=-1
  for p in sorted(ps):
   th=1 if p in [2,3] or p in bp else d7 if p==7 else ds[p]['D']
   chi=1 if p==2 else leg(th,p)
   if p==2:
    assert (r+s+1)%8==0 and (r*s)%32==0
    f,w=1,-1
   elif p==3 and k%3==0:
    assert (r%9,s%9)==(0,0) and {r//9%3,s//9%3}=={1,2}
    f,w=0,1
   elif p==3:
    assert r%3==s%3==2;f,w=1,1
   elif p in bp:f,w=2,leg(-1,p)
   elif p in ds1:
    e=ds1[p]
    if e%2:f,w=2,leg(-1,p)
    else:
     assert (r//p**e)%p==(s//p**e)%p!=0
     f,w=1,-leg(r//p**e,p)
   else:
    assert r%p==0 and s%p
    f,w=1,-leg(-s,p)
   z=w*(chi**f);sign*=z
   out.append([p,f,w,chi,z])
  dirs[k]=dict(local_table=out,base_root=-prod(v[2] for v in out),actual_root=sign)
 assert [dirs[k]['actual_root'] for k in (4,12,16,48)]==[1,1,-1,-1]
 return dict(D7=d7,actual_orbit_mod_p=ds,curves=dirs)
if __name__=='__main__':print(json.dumps(main(),indent=2))
