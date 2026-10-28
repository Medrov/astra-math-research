import itertools, random, collections
triples=list(itertools.combinations(range(1,8),3))
base=[t for t in triples if t[0]^t[1]^t[2]==0]
reps={}
for p in itertools.permutations(range(1,8)):
    lines=tuple(sorted(tuple(sorted(p[i-1] for i in t)) for t in base))
    if lines not in reps: reps[lines]=p
planes=list(reps)
bits=[[int(t in plane) for t in triples] for plane in planes]
diffs=[[k for k in range(35) if bits[i][k]!=bits[j][k]] for i in range(30) for j in range(i)]
print('planes',len(planes),'full distance',min(map(len,diffs)))
for target in [1,3,5]:
    best=list(range(35))
    for run in range(2000):
        subset=set(range(35)); order=list(subset); random.shuffle(order)
        for k in order:
            if all(sum(j in subset for j in d)-(k in d)>=target for d in diffs):subset.remove(k)
        if len(subset)<len(best):best=sorted(subset)
    print('target',target,'length',len(best),'indices',best,'triples',[triples[k] for k in best])
print('reps',list(reps.values()))
