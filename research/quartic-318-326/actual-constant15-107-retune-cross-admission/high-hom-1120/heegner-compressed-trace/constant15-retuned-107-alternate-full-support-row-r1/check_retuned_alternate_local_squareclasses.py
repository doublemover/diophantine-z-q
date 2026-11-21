"""Literal retained ramified theta rows, including two vanishing sigma arms."""
import json
B=204618888056724185
e=2952271997968816765
a,b,z=31859917667562016618135,59323292900802,9995282212057
assert a*a-B*b*b==e*z*z
def leg(x,p):
    z=pow(x%p,(p-1)//2,p)
    return -1 if z==p-1 else z
def root(x,p):
    assert p%4==3 and leg(x,p)==1
    r=pow(x%p,(p+1)//4,p)
    assert (r*r-x)%p==0
    return r
rows=[]
for p,c0,dc in ((131,54,82),(6551,2194,684),(2470991,722614,2223081)):
    assert e%p==0 and (e//p)%p and z%p and leg(5,p)==1
    t=((1-B*c0*c0)//p-dc)*pow(2*B*c0,-1,p)%p
    c=c0+p*t
    assert (1-B*c*c)%p**2==p*dc
    s=-pow(c,-1,p)%p
    s+=p*(((B-s*s)//p)*pow(2*s,-1,p)%p)
    assert (s*s-B)%p**2==0 and s*c%p==p-1
    j=root(-5*pow((e//p)*dc,-1,p),p) # residue of p sqrt(-5/e/delta)
    L1=s*(a-s*b)%p**2
    v=int(L1%p==0)
    assert L1//p**v%p
    out=[]
    for J in (j,-j):
        L2=((a+B*c*b)*s-9*B*(b+c*a)-4*p*(e//p)*dc*z*s*J)%p**2
        if (L2//p**v)%p==0:continue
        assert L2%p**v==0
        ang=(L1//p**v)*(L2//p**v)%p
        assert leg(ang,p)==leg(10,p)
        out.append(dict(j_times_p_mod_p=J%p,L1_stripped=L1//p**v%p,
                        L2_stripped=L2//p**v%p,product_symbol=leg(ang,p)))
    assert out
    rows.append(dict(p=p,retained_c_mod_p2=c,sigma_minus_mod_p=(a-s*b)%p,
                     both_tangent_depth=v,branches=out))
# At 2 test all allowed c mod 16 and both possible odd roots on each branch.
assert B%8==1 and e%8==5 and b%2==0 and (a*z)%2
dyadic=[]
for c in (4,12):
    m=16;d=(1-B*c*c)%m
    ry=(1-4*B)*pow(e,-1,m)%m
    rz=(1-324*B)*pow(e*d,-1,m)%m
    assert ry==rz
    roots=[Y for Y in range(1,8,2) if (Y*Y-ry)%m==0]
    Y=next(Y for Y in roots if (a-e*z*Y-2*B*b)%4==2)
    Z=Y
    L1=(a-e*z*Y-2*B*b)%8
    L2=(a+B*c*b-18*B*(b+c*a)-e*d*z*Z)%8
    assert L1==L2 and L1 in (2,6)
    assert (L1//2)*(L2//2)%4==1
    dyadic.append(dict(c_mod16=c,Y_equals_Z_mod8=Y,L1_mod8=L1,L2_mod8=L2))
print(json.dumps(dict(ramified_theta_rows=rows,dyadic=dyadic),sort_keys=True,indent=2))
