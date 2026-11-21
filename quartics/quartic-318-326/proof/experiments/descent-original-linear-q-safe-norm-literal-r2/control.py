from fractions import Fraction as Q
cases=0; pairs=0; exact=[0,0]; gap=-1
for p in (3,5,7,11,13,17,19,23,29,31,37,41,43,47):
    char = 1 if p%4==1 else -1
    for n in range(1,p):
        full=[(a,b) for a in range(p) for b in range(p) if (a*a+b*b-n)%p==0]
        bad=[set((a,b) for a,b in full if ((a+d)**2+b*b)%p==0) for d in (-1,1)]
        safe=set(full)-bad[0]-bad[1]
        assert len(full)==p-char
        assert len(bad[0]) <= 2 and len(bad[1]) <= 2
        assert Q(1)-Q(4,len(full)) <= Q(len(safe),len(full))
        for j in range(2): exact[j]+=len(bad[j])==2
        gap=max(gap,len(full)-len(safe))
        pairs+=len(full)
        cases+=1
assert gap==4
print(cases,pairs,tuple(exact),gap)
