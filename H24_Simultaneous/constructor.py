"""Explicit finite H24 Bellman constructor, Horn-CNF return, binary Cayley gap.
No SAT oracle, no proof-tree enumeration in the producer. Verification checks
Bellman inequalities and tight backpointers, not an externally supplied optimum.
The logical work ledger counts rule visits/premise accesses; it is NOT a measured
Turing bit clock. See README for the proved implementation cost envelope.
"""
from dataclasses import dataclass
from itertools import product, permutations
import random, json

@dataclass(frozen=True)
class Rule:
    head: int
    premises: tuple[int, ...]
    cost: int = 1

@dataclass
class Certificate:
    value: list[int | None]
    chosen: list[int | None]
    scans: int
    premise_reads: int
    rounds: int


def check_rules(n, rules):
    assert n >= 0
    for r in rules:
        assert 0 <= r.head < n and r.cost > 0
        assert all(0 <= p < n for p in r.premises)


def solve(n: int, rules: list[Rule]) -> Certificate:
    """Synchronous min-plus height fold. None is +infinity, not a zero.
    At most n rounds by the positive-charge cycle-removal lemma.
    Each old entry is read from the previous round; original ties can be
    reconstructed by scanning all rules against final values.
    """
    check_rules(n, rules)
    old = [None] * n
    scans = reads = rounds = 0
    for _ in range(n):
        new = old.copy()
        for r in rules:
            scans += 1
            vals = [old[p] for p in r.premises]
            reads += len(vals)
            if any(v is None for v in vals):
                continue
            cost = r.cost + sum(vals)
            if new[r.head] is None or cost < new[r.head]:
                new[r.head] = cost
        rounds += 1
        if new == old:
            old = new
            break
        old = new
    chosen = [None] * n
    for i, r in enumerate(rules):
        scans += 1
        vals = [old[p] for p in r.premises]
        reads += len(vals)
        if any(v is None for v in vals):
            continue
        if r.cost + sum(vals) == old[r.head] and chosen[r.head] is None:
            chosen[r.head] = i
    result = Certificate(old, chosen, scans, reads, rounds)
    verify(n, rules, result)
    return result


def verify(n, rules, cert):
    """Local, complete certificate check. Closed productive subset +
    lower-bound inequalities for ALL rules + a decreasing tight rule for
    every productive head. None means no finite proof; proved by induction
    on any hypothetical finite proof. Tight rules recursively attain V.
    """
    check_rules(n, rules)
    v, chosen = cert.value, cert.chosen
    assert len(v) == len(chosen) == n
    for j in range(n):
        if v[j] is None:
            assert chosen[j] is None
        else:
            assert isinstance(v[j], int) and v[j] > 0
            k = chosen[j]
            assert isinstance(k, int) and 0 <= k < len(rules)
            r = rules[k]
            assert r.head == j
            assert all(v[p] is not None and v[p] < v[j] for p in r.premises)
            assert v[j] == r.cost + sum(v[p] for p in r.premises)
    for r in rules:
        if all(v[p] is not None for p in r.premises):
            assert v[r.head] is not None
            assert v[r.head] <= r.cost + sum(v[p] for p in r.premises)


def tight_rules(rules, cert):
    v = cert.value
    return [i for i,r in enumerate(rules) if all(v[p] is not None for p in r.premises)
            and v[r.head] == r.cost + sum(v[p] for p in r.premises)]


def proof_dag(target, rules, cert):
    """Return one selected original rule per demanded judgment, with strictly
    increasing potential topological order. No expanded proof tree printed."""
    if cert.value[target] is None:
        return None
    seen, stack = set(), [target]
    while stack:
        j = stack.pop()
        if j in seen:
            continue
        seen.add(j)
        stack.extend(rules[cert.chosen[j]].premises)
    return [(j, cert.chosen[j]) for j in sorted(seen, key=lambda j:(cert.value[j],j))]


def horn(n, clauses):
    """Each input Horn clause is (tuple of positive body variable indices,
    head index or None for false). Rule i preserves original clause i.
    Return least model or selected original rule DAG for bottom.
    """
    assert all(h is None or 0 <= h < n for _,h in clauses)
    assert all(0 <= p < n for b,_ in clauses for p in b)
    rules = [Rule(n if h is None else h, tuple(b)) for b,h in clauses]
    c = solve(n+1,rules)
    if c.value[n] is None:
        a = tuple(c.value[i] is not None for i in range(n))
        assert all(not fails(a,cl) for cl in clauses)
        return True,a,c
    dag = proof_dag(n,rules,c)
    assert dag is not None
    return False,dag,c


def fails(a, clause):
    b,h = clause
    return all(a[p] for p in b) and (h is None or not a[h])


def failure_from_dag(a, clauses, dag):
    """Given any assignment, decode a failed ORIGINAL clause index from
    the Horn refutation, without traversing expanded proof occurrences."""
    for j,k in dag:
        if fails(a,clauses[k]):
            return k
    raise AssertionError('a bottom derivation must expose a failed clause')

# Finite fields F_{2^k} for an explicit small-bias Cayley probe set.
def degree(f): return f.bit_length()-1

def modpoly(a,b):
    while a and degree(a)>=degree(b): a ^= b << (degree(a)-degree(b))
    return a

def irreducible(k):
    # Deterministic trial division. q=2^k=O(m); this is polynomial in m.
    for f in range((1<<k)|1,1<<(k+1),2):
        if all(modpoly(f,g) for d in range(1,k//2+1)
               for g in range(1<<d,1<<(d+1))): return f
    raise AssertionError('irreducible polynomial exists at every degree')

def mul(a,b,f,k):
    ans=0
    while b:
        if b&1: ans ^= a
        b >>= 1; a <<= 1
        if a & (1<<k): a ^= f
    return ans

def parity(x): return x.bit_count() & 1

def masks(m):
    """Multiset of q^2 masks on m original failed-clause bits. Includes zero
    masks/loops and multiplicities, intentionally. The construction is not
    claimed to be a relative sparsifier of the cube or a Ramanujan graph.
    """
    assert m>=1
    k=max(1,(2*m-1).bit_length()); q=1<<k; f=irreducible(k)
    out=[]
    for a in range(q):
        powers=[1]
        for j in range(1,m): powers.append(mul(powers[-1],a,f,k))
        for b in range(q):
            out.append(sum(parity(b&p)<<j for j,p in enumerate(powers)))
    return q,out

def gap_count(y, ss): return sum(parity(y&s) for s in ss)

def tests():
    rng=random.Random(20261125)
    gtests=0; htests=0; assignment_checks=0; mask_checks=0
    # Independent extra-height iteration to test the height bound; test only.
    for _ in range(600):
        n=rng.randrange(1,9)
        rules=[Rule(rng.randrange(n),tuple(rng.randrange(n) for _ in range(rng.randrange(4))),rng.randrange(1,10))
               for _ in range(rng.randrange(25))]
        c=solve(n,rules)
        prev=[None]*n
        for h in range(2*n+3):
            byhead=[[] for _ in range(n)]
            for r in rules:
                if all(prev[p] is not None for p in r.premises):
                    byhead[r.head].append(r.cost+sum(prev[p] for p in r.premises))
            prev=[min(xs) if xs else None for xs in byhead]
        assert prev==c.value
        gtests+=1
    for _ in range(500):
        n=rng.randrange(0,8)
        cs=[(tuple(rng.randrange(n) for _ in range(rng.randrange(4))) if n else (),
             rng.randrange(n) if n and rng.randrange(3) else None) for _ in range(rng.randrange(20))]
        sat,w,c=horn(n,cs)
        models=[]
        for a in product((False,True),repeat=n):
            valid=not any(fails(a,cl) for cl in cs)
            if valid: models.append(a)
            if not sat:
                i=failure_from_dag(a,cs,w); assert fails(a,cs[i])
            assignment_checks+=1
        assert sat==bool(models)
        if sat: assert w in models and all(all(not x or y for x,y in zip(w,a)) for a in models)
        htests+=1
    for m in range(1,10):
        q,ss=masks(m); assert len(ss)==q*q and gap_count(0,ss)==0
        for y in range(1,1<<m):
            w=gap_count(y,ss)
            assert 4*w>=q*q and 2*w<=q*q
            # Exact character average has numerator q times a root count.
            assert (q*q-2*w)%q==0 and (q*q-2*w)//q<=m-1
            mask_checks+=1
    # Exact order-independence counts for the native symmetric frame groups.
    commuting={}
    for n,expected in [(3,18),(4,120),(5,840)]:
        ps=list(permutations(range(n)))
        yes=sum(all(p[q[i]]==q[p[i]] for i in range(n)) for p in ps for q in ps)
        assert yes==expected
        commuting[f'S{n}']={'commuting_pairs':yes,'ordered_pairs':len(ps)**2}
    # A linear-size proof DAG with exponential expanded minimum tree work.
    n=100
    rules=[Rule(0,())]+[Rule(i,(i-1,i-1)) for i in range(1,n)]
    c=solve(n,rules); assert c.value[-1]==2**n-1
    dag=proof_dag(n-1,rules,c); assert len(dag)==n
    return {'random_grammar_cases':gtests,'random_horn_cases':htests,
            'horn_assignment_checks':assignment_checks,'nonzero_mask_checks':mask_checks,
            'commuting_frames':commuting,
            'doubling_tree_example':{'judgments':n,'min_tree_cost':str(c.value[-1]),'dag_nodes':len(dag),
            'rule_scans':c.scans,'premise_reads':c.premise_reads,'rounds':c.rounds},
            'lean_kernel_replay':'not run: executable unavailable in current environment'}

if __name__=='__main__': print(json.dumps(tests(),indent=2))
