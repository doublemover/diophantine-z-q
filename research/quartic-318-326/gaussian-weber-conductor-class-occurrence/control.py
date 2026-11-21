from itertools import product
count=0
for m in range(2,74,2):
    for a,b,x,y in product(range(-4,5),repeat=4):
        ga,gb=a+m*x,b+m*y
        D=ga*ga+gb*gb-(a*a+b*b)
        assert D==2*m*(a*x+b*y+(m//2)*(x*x+y*y))
        assert (ga*ga+gb*gb)% (2*m)==(a*a+b*b)%(2*m)
        count+=1
print('exact even-norm congruence cases:',count)
