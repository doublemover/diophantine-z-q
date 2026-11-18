from math import gcd
import json
import original_probe as I
import base_check as B
p=83
v=I.probe(p,forceM=11861136)
assert v and v['D']==61 and (v['UH2'][0]**2-2*v['UH2'][1]**2)%p
beta=I.beta
leg=lambda x:pow(x%p,(p-1)//2,p)
d=v['D']; assert leg(beta)==leg(-2*d)==1
assert B.main()['beta']==beta==I.beta
a,b,c=B.main()['basis'];assert (b[0]*c[0],b[1]//c[1])==(beta,1)
signs=lambda z:[int(leg(j)==p-1) for j in z]
rows=[a,b,[beta,1]]
assert list(map(signs,rows))==[[1,1],[0,1],[0,0]]
roots=[(s,z) for s in range(p) for z in range(p) if (9-beta*s*s)%p==0 and (beta*s*s+d*z*z-1)%p==0]
assert len(roots)==4 and all(s*z%p for s,z in roots)
print(json.dumps({'actual_probe':v,'loc_q0':[{'pair':z,'nonresidue_bits':signs(z)} for z in rows],'roots_using_D_conic':roots,'base_sel2_dim':len(B.main()['basis'])},indent=2))
