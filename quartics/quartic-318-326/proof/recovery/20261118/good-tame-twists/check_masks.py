from itertools import product
for e in product((0,1),repeat=4):
 if not any(e):continue
 n=[]
 for j in range(5):
  c=[e[i] for i in range(4) if i!=j] if j<4 else [e[i]^e[0] for i in (1,2,3)]
  fixed=sum(all(a==a^b for a,b in zip(label,c)) for label in product((0,1),repeat=3))
  n.append(fixed)
 assert n==[8 if (sum(e)==1 and j<4 and e[j]) or (sum(e)==4 and j==4) else 0 for j in range(5)]
print('PASS 15 masks, five branch sections, eight labels per geometric branch.')
