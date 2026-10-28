"""Independent finite experiment for the octonion incidence proof.

Uses integer quaternion-pair arithmetic and enumerates every relabeling.
The JSON output is experiment evidence, not a replacement for the Lean proof.
"""
from itertools import combinations, permutations, product
import json
from pathlib import Path


def qadd(x, y):
    return tuple(a + b for a, b in zip(x, y))


def qneg(x):
    return tuple(-a for a in x)


def qstar(x):
    return (x[0], -x[1], -x[2], -x[3])


def qmul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


def omul(x, y):
    a, b = x
    c, d = y
    return (qadd(qmul(a, c), qneg(qmul(d, qstar(b)))),
            qadd(qmul(qstar(a), d), qmul(c, b)))


zero = (0, 0, 0, 0)
units = [tuple(int(j == i) for j in range(4)) for i in range(4)]
basis = [(units[i], zero) for i in range(1, 4)] + [(zero, u) for u in units]
triples = list(combinations(range(7), 3))
index = {triple: i for i, triple in enumerate(triples)}


def associative(t):
    x, y, z = (basis[i] for i in t)
    return omul(omul(x, y), z) == omul(x, omul(y, z))


lines = [t for t in triples if associative(t)]
assert lines == [t for t in triples if (t[0]+1) ^ (t[1]+1) ^ (t[2]+1) == 0]
for i, j, k in product(range(7), repeat=3):
    expected = i == j or i == k or j == k or ((i+1) ^ (j+1) ^ (k+1)) == 0
    assert associative((i, j, k)) == expected
planes = sorted({tuple(sorted(index[tuple(sorted(p[i] for i in t))] for t in lines))
                 for p in permutations(range(7))})
assert len(planes) == 30
assert all(sum(i in plane for plane in planes) == 6 for i in range(35))

probe_sets = {
    "ten_exact": [123,127,135,137,157,236,256,267,356,567],
    "eighteen_one_error": [124,126,145,147,156,167,234,236,245,247,256,267,
                           345,347,356,367,457,567],
}
results = {}
for name, labels in probe_sets.items():
    probes = [index[tuple(int(c)-1 for c in str(label))] for label in labels]
    codes = [tuple(int(probe in plane) for probe in probes) for plane in planes]
    distances = [sum(a != b for a, b in zip(x, y)) for x, y in combinations(codes, 2)]
    assert len(set(codes)) == 30
    if name == "eighteen_one_error":
        assert min(distances) >= 3
        balls = {}
        for i, code in enumerate(codes):
            for changed in [None, *range(len(code))]:
                received = tuple(bit ^ int(j == changed) for j, bit in enumerate(code))
                assert received not in balls
                balls[received] = i
        assert len(balls) == 30 * 19
    results[name] = {
        "triples_one_based": [list(map(int, str(label))) for label in labels],
        "distinct_signatures": len(set(codes)),
        "minimum_hamming_distance": min(distances),
        "signatures": ["".join(map(str, code)) for code in codes],
    }

report = {
    "method": "integer Cayley-Dickson arithmetic; exhaustive 7! relabelings",
    "proof_status": "experiment only; see Lean theorems for formal verification",
    "base_lines_one_based": [[i+1 for i in t] for t in lines],
    "distinct_incidence_patterns": len(planes),
    "ordered_basis_triples_checked": 343,
    "each_triple_occurs_in_patterns": 6,
    "probe_sets": results,
}
destination = Path(__file__).resolve().parents[1] / "verification/probe_experiment.json"
destination.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({name: {k: v for k, v in value.items() if k != "signatures"}
                  for name, value in results.items()}, indent=2))
