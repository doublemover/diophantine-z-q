from sympy import symbols,expand
W,P,t,T=symbols('W P t T')
for d in (-1,1):
 delta=(1+d)//2
 assert d*(32-76832)//16==-75*d*64 and d*(0-32)//4==-8*d
 assert expand((2*W)**2+2*(1+2*T)*(2*W)+2*(2*T)**2+4*(2*T)+4*delta-4*(W**2+(1+2*T)*W+2*T**2+2*T+delta))==0
 assert expand((t*W)**2+(t*P)*(1+t)*t*W+t*P*t**2+(t*P)**2*t+(t*P)**2*delta-t**2*(W**2+P*(1+t)*W+t*P+t*P**2+delta*P**2))==0
print('two exact unit signs; 2- and t-direction identities; four exponent drops verified:',list(range(8,-1,-2)))
