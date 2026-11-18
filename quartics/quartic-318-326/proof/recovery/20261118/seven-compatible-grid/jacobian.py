def jmul(p,A,pt,n):
    O=(1,1,0)
    def dbl(P):
        X,Y,Z=P
        if not Y or not Z:return O
        yy=Y*Y%p;s=4*X*yy%p;m=(3*X*X+A*pow(Z,4,p))%p
        x=(m*m-2*s)%p
        return x,(m*(s-x)-8*yy*yy)%p,2*Y*Z%p
    def mixed(P,Q):
        X,Y,Z=P;x,y=Q
        if Z==0:return (x,y,1)
        z2=Z*Z%p;u=x*z2%p;v=y*z2*Z%p
        h=(u-X)%p;r=(v-Y)%p
        if h==0:return dbl(P) if r==0 else O
        h2=h*h%p;h3=h2*h%p;bh=X*h2%p
        xx=(r*r-h3-2*bh)%p
        return xx,(r*(bh-xx)-Y*h3)%p,Z*h%p
    R=O
    for b in bin(n)[2:]:
        R=dbl(R)
        if b=='1':R=mixed(R,pt)
    x,y,z=R
    if z==0:return None
    iz=pow(z,-1,p)
    return [x*iz**2%p,y*iz**3%p]
