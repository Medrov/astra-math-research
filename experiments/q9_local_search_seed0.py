import itertools, random, time
T=list(itertools.combinations(range(7),3)); ti={v:i for i,v in enumerate(T)}
base=[t for t in T if (t[0]+1)^(t[1]+1)^(t[2]+1)==0]
P=sorted({tuple(sorted(ti[tuple(sorted(p[i] for i in t))] for t in base)) for p in itertools.permutations(range(7))})
M=[sum(1<<i for i in p) for p in P]
rng=random.Random(0)
def score(S):
 vals=[m&S for m in M]
 return len(set(vals))
best=0; bests=None
for run in range(1000):
 S=sum(1<<i for i in rng.sample(range(35),9))
 q=score(S)
 for step in range(100):
  ins=[i for i in range(35) if S>>i&1]; outs=[i for i in range(35) if not S>>i&1]
  a=rng.choice(ins);b=rng.choice(outs);S2=S^(1<<a)^(1<<b);q2=score(S2)
  if q2>=q or rng.random()<0.02:S,q=S2,q2
  if q>best:best,bests=q,S
  if best==30:break
 if best==30:break
print('planes',len(P),'best distinct',best,'queries',[tuple(i+1 for i in T[k]) for k in range(35) if bests>>k&1], 'run',run)
