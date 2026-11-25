"""Actual adapter to the retained self-witnessing H24 source.
Use guarded_construct and guarded_return instead of direct construct/evidence.
Do not pass arbitrary receipt lists as authority to prove an unrelated claim.
"""
from dataclasses import dataclass
from pathlib import Path
import sys
import invariants as inv
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'retained'/'h24'))
import self_witness as original

@dataclass(frozen=True)
class CNFReturn:
    proof: object
    result: inv.Receipt
    assignment: tuple[tuple[int,int],...]
    minimum_failed_clauses: int | None
    ground_count: int | None
    operational_clock: inv.Receipt
    @property
    def source_belnap(self):
        if self.result.status!=inv.Status.PROVED:return (0,0)
        return (1,0) if self.minimum_failed_clauses==0 else (0,1)

def guarded_return(n,clauses,proof):
    """Checks the actual supplied original CNF and the complete marked H24 DAG.
    A malformed certificate does NOT refute the mathematical CNF.
    """
    clauses=tuple(map(tuple,clauses)); scope='original finite 3-CNF, minimum charge and all ground marks'
    try:
        if type(n)!=int or n<0 or any(len(c)>3 or any(type(l)!=int or not 1<=abs(l)<=n for l in c) for c in clauses):raise ValueError('invalid original CNF')
        if not isinstance(proof,original.Proof) or proof.n!=n or proof.clauses!=clauses:raise ValueError('original question/proof binding mismatch')
        m,w,count=original.verify(proof)
        if set(w)!=set(range(1,n+1)) or any(type(b)!=int or b not in (0,1) for b in w.values()):raise ValueError('invalid original witness')
        # original.verify recomputes every sum/product and native ground projector.
        status=inv.yes('H24.ORIGINAL_MINIMUM_RETURN',scope,f'minimum={m}',f'ground count={count}',f'DAG nodes={len(proof.nodes)}')
        return CNFReturn(proof,status,tuple(sorted(w.items())),m,count,inv.claim_universal_clock())
    except (ValueError,TypeError,AttributeError,IndexError,AssertionError,KeyError) as e:
        return CNFReturn(proof,inv.no('H24.CERTIFICATE_VALID',scope,e),(),None,None,inv.claim_universal_clock())

def guarded_construct(n,clauses):
    clauses=tuple(map(tuple,clauses))
    return guarded_return(n,clauses,original.construct(n,clauses))

@dataclass(frozen=True)
class ClockReturn:
    history: tuple
    invariant: inv.Receipt
    uniform_clock: inv.Receipt

def guarded_history(r:inv.HistoryRequest):
    """Returns the actual closed orbit only after checking the entire marked seam.
    A stationary finite history is not a physical energy or all-input clock certificate.
    """
    verdict=inv.history(r)
    if verdict.status!=inv.Status.PROVED:return ClockReturn((),verdict,inv.claim_universal_clock())
    x=inv.exact(r.initial); out=[inv.s.ImmutableMatrix(x)]
    for U in r.transitions[:-1]:
        x=inv.exact(U)*x; out.append(inv.s.ImmutableMatrix(x))
    return ClockReturn(tuple(out),verdict,inv.claim_universal_clock())

def guarded_transport(r:inv.CovarianceRequest, edges=None, phi=None):
    sem=inv.covariance(r)
    charge=inv.opn('H24.WORK_BOUNDARY_COVARIANCE','actual charge transport','no edge ledger supplied') if edges is None or phi is None else inv.boundary_charge(edges,phi)
    return sem,charge
