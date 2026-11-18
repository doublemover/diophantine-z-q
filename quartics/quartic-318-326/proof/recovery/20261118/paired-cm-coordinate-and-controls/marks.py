"""Exact independent arithmetic verification of both marked rational witnesses and translated pair."""
from fractions import Fraction as F
import json
W=[
(1751,[248083,831147,352525],14248),
(800207,[780843691442385777738097969939490483889666027852021839904535806689927358878144467452336857237049782701777067,
2585017722007009761781753598590842997827881286184052936083411715613425847506172745870688968191374219128727805,
1122334681193740843423736578105914196043199494434477259936393919785737616802949289402268026190962477919986059],
2145319754335412384769167447507805529869820808850737281793471020248296272110160646658893008012002769156472)]
def f(e,x):return x*(x-e)*(x+3*e)
pts=[]
for d,nums,den in W:
    u,v,w=[F(j,den) for j in nums];x=17*u*u;y=17*u*v*w
    assert x-d==v*v and x+3*d==17*w*w and y and y*y==f(d,x)
    pts.append((u,y))
c=F(204,439715);b=c*c;B=17*b;h=B*F(20569,439715);V=B*B*(1-b/17)
assert B==17*c*c and V==457*h*h
(u,y),(U,Y)=pts
E=1751*(c/u)**2;S=U*h/u;y1=y*(c/u)**3;y2=Y*(c*h/u)**3
assert E*S*y1*y2 and y1*y1==f(E,B) and y2*y2==f(E*V,B*S*S)
print(json.dumps(dict(marked_points=W,b=str(b),point_pair={n:str(z) for n,z in zip(['E','S','y1','y2'],[E,S,y1,y2])}),indent=2))
