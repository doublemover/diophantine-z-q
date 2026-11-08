#!/usr/bin/env python3
"""Independent exact rational check of all four actual affine coordinate maps.
No Lean/compiler execution, external packages, network, or source edits.
"""
from fractions import Fraction as Q
from pathlib import Path
import ast, json, re, sys
repo=Path(sys.argv[1]) if len(sys.argv)>1 else Path('diophantine-z-q')
p=repo/'quartics/quartic-318-326/proof/progress'
def rational(n):
    if isinstance(n,ast.Constant) and isinstance(n.value,int): return Q(n.value)
    if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub): return -rational(n.operand)
    if isinstance(n,ast.BinOp) and isinstance(n.op,ast.Div): return rational(n.left)/rational(n.right)
    raise ValueError(ast.dump(n))
def values(file,name):
    text=(p/file).read_text()
    match=re.search(r'def '+name+r'\b[^\n]*?(?:\n\s*)?:=\s*!\[([^]]+)\]',text)
    assert match,name
    return [rational(ast.parse(x.strip(),mode='eval').body) for x in match.group(1).split(',')]
def mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
f='SourceTwistArithmetic318.lean'
cs=values(f,'constants'); us=values(f,'coordinateScale'); As=values(f,'publishedA'); Bs=values(f,'publishedB')
oldAs=values(f,'cubicA');oldBs=values(f,'cubicB');js=values(f,'jacobianTwist')
contacts=values('LinearContactSquareclass318.lean','contacts')
rows=[]
for i in range(4):
    other=[j for j in range(4) if j!=i]
    C=Q(1)
    for j in other:C*=cs[j]
    m=sum((contacts[j] for j in other),Q(0))/3
    u=us[i];A=As[i];B=Bs[i]
    assert C!=0 and u!=0
    k=u*u/C; l=u**3/C
    # In the published coordinate ring: t=k*x+m, z=l*y.
    image=[C]
    for j in other:image=mul(image,[m-contacts[j],k])
    assert image==[l*l*B,l*l*A,Q(0),l*l]
    # Inverse polynomial coordinate maps: x=(t-m)/k, y=z/l.
    ik=C/u**2; il=C/u**3
    assert k*ik==1 and ik*k==1 and l*il==1 and il*l==1
    assert ik*m-ik*m==0 and k*(-ik*m)+m==0
    depressed=[Q(1)]
    for j in other:depressed=mul(depressed,[m-contacts[j],Q(1)])
    assert depressed==[oldBs[i],oldAs[i],Q(0),Q(1)]
    assert C==js[i]*u*u
    assert C*C*oldAs[i]==u**4*A and C**3*oldBs[i]==u**6*B
    delta=-16*(4*A**3+27*B*B)
    assert delta!=0
    rows.append(dict(omitted=i,contact=str(contacts[i]),C=str(C),centroid=str(m),u=str(u),
       t_image_x_coefficient=str(k),z_image_y_coefficient=str(l),
       inverse_x_coefficient=str(ik),inverse_y_coefficient=str(il),discriminant=str(delta),
       polynomial_identity=True,both_inverse_compositions=True))
print(json.dumps({'status':'PASS','method':'exact fractions; coefficients parsed from pinned Lean sources',
  'all_four_indices':rows,'scope':'affine coordinate relations and two inverse compositions only'},indent=2))
