import itertools,random
T=list(itertools.combinations(range(7),3));ti={v:i for i,v in enumerate(T)};B=[t for t in T if (t[0]+1)^(t[1]+1)^(t[2]+1)==0]
P=sorted({tuple(sorted(ti[tuple(sorted(p[i] for i in t))] for t in B)) for p in itertools.permutations(range(7))});M=[sum(1<<i for i in p) for p in P]
r=random.Random(17)
for n in [10,11,12]:
 best=0
 for run in range(3000):
  S=sum(1<<i for i in r.sample(range(35),n));q=len({m&S for m in M})
  for step in range(200):
   a=r.choice([i for i in range(35) if S>>i&1]);b=r.choice([i for i in range(35) if not S>>i&1]);U=S^(1<<a)^(1<<b);v=len({m&U for m in M})
   if v>=q or r.random()<0.02:S,q=U,v
   if q>best:best,bests=q,S
   if best==30:break
  if best==30:break
 print(n,best,[tuple(i+1 for i in T[k]) for k in range(35) if bests>>k&1],flush=True)
