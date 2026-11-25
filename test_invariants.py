from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sympy as s
import invariants as v
import guarded_prover as h
from collections import Counter

results=[]
def check(r,status):
    assert r.status==status,(r,status)
    results.append(r.json());return r
Y,N,O=v.Status.PROVED,v.Status.REFUTED,v.Status.OPEN
# Factorized dissipation in original metric; A on a positive-dimensional mode.
I=s.eye(4); G,R,S=v.G,v.R,v.S
A=s.I*I; B=s.Matrix([[0,1,0,0]]); D=-v.dag(B,G,s.eye(1))*B
x=I[:,0]; mode=v.ModeRequest(A,D,B,G,x,1)
cert=check(v.persistent_mode(mode),Y); assert v.replay(v.persistent_mode,mode,cert)
check(v.persistent_mode(replace(mode,x=I[:,1])),N)
check(v.persistent_mode(replace(mode,D=I)),O)
check(v.persistent_mode(replace(mode,x=s.zeros(4,1))),O)
# Pure dissipative generator cannot supply nonzero frequency on a nonzero vector.
check(v.persistent_mode(replace(mode,A=s.zeros(4))),N)
# Stationary ground observable and a nonstationary control.
P=s.diag(0,1,1,0); K=(P+P*S)/2; rho=(P-P*S)/2
check(v.stationary_observation(v.StationaryRequest(K,rho,S,G)),Y)
check(v.stationary_observation(v.StationaryRequest(K,rho*2,S,G)),O)
# Explicit closed and open history; compare actual returned orbit.
for us,x,st in [((R,R,R),I[:,1],Y),((R,I,I),I[:,1],N),((R,I,I),I[:,0],Y)]:
    r=h.guarded_history(v.HistoryRequest(us,x,G));check(r.invariant,st)
    assert bool(r.history)==(st==Y) and r.uniform_clock.status==O
    if r.history:assert us[-1]*r.history[-1]==r.history[0]
# Original native covariance and a basis counterexample.
check(v.covariance(v.CovarianceRequest(R,S,R*S*R.inv(),G)),Y)
check(v.covariance(v.CovarianceRequest(R,S,S,G)),N)
check(v.covariance(v.CovarianceRequest(2*I,S,S,G)),O)
sem,work=h.guarded_transport(v.CovarianceRequest(R,S,R*S*R.inv(),G));assert sem.status==Y and work.status==O
# Strict locality fails for reversible midpoint even at exact rational h.
J=s.Matrix([[0,-1,0],[1,0,-1],[0,1,0]]); a=s.Rational(1,3)
U=(s.eye(3)-a*J).inv()*(s.eye(3)+a*J); assert U.T*U==s.eye(3)
check(v.locality(U,1),N);check(v.locality(U,2),Y)
check(v.locality(s.eye(3),0),Y)
# Native winding work, alias, clock capacity and commutator.
for w in range(-20,21):check(v.winding(9,w,[1 if w>=0 else -1]*(9*abs(w))),Y)
check(v.winding(9,1,[1]*8),N);check(v.winding(9,1,[1]*10+[-1]),N)
check(v.winding_alias(9,1,10),N);check(v.winding_alias(9,1,2),Y)
check(v.finite_perfect_clock(4,9),N);check(v.finite_perfect_clock(9,9),Y)
check(v.finite_clock_ccr(I,R,G),N)
check(v.two_level_orthogonal(s.Rational(1,2),-1),Y)
check(v.two_level_orthogonal(s.Rational(1,3),-1),N)
# Exact arbitrarily small positive gap counterexamples.
for f in [Q(1),Q(1,100),Q(1,10**30)]:check(v.uniform_gap_counterexample(f),N)
check(v.gap_claim(1,Q(1,100)),O)
check(v.scale_identification(2,1),N);check(v.scale_identification(1,1),O)
check(v.vacuum_flux(v.FluxRequest([1,0,0],[0,1,0],[0,0,1])),Y)
check(v.vacuum_flux(v.FluxRequest([1,0,0],[0,0,0],[0,0,1])),Y)
check(v.classical_energy_floor([1,0,0],[0,1,0],Q(1,10**20)),N)
# Evidence and dyadic guards.
for k in range(2,33):check(v.dyadic_zero_claim(k),N);check(v.dyadic_gram_claim(k),N)
check(v.projector_involution(P,G),N);check(v.projector_involution(I,G),Y)
check(v.posterior([1,1],[0,0]),N);check(v.posterior([1,1],[1,2]),Y)
check(v.independent_evidence_claim(),N);check(v.moment_sufficiency_claim(),N)
check(v.clock_no_hit([0]*64),N);check(v.bool_diagonal(),N);check(v.no_work_from_identity(),N)
# Exact H24 ledger and no invented work equality.
check(v.haar_owner_integral((('a',4,3),('b',100,9)),2),Y)
check(v.haar_owner_integral((('a',4,3),('a',5,7))),N)
check(v.boundary_charge((('a','b',4,5),('b','a',4,3)),{'a':0,'b':1}),Y)
check(v.boundary_charge((('a','b',4,5),('b','a',4,4)),{'a':0,'b':1}),N)
# The actual finite transition ledger must be continuous, paid, and terminal.
t1=v.Tick('input','acquired',2,5,3,'acquire');t2=v.Tick('acquired','checked',3,3,0,'verify')
req=v.TraceRequest('input',(t1,t2),'checked',5,(('input','acquired',2,'acquire'),('acquired','checked',3,'verify')),('checked',))
cert=check(v.check_trace(req),Y);assert v.replay(v.check_trace,req,cert)
check(v.check_trace(replace(req,ticks=(replace(t1,reserve_after=4),t2))),N)
check(v.check_trace(replace(req,ticks=(t1,))),N)
check(v.check_trace(replace(req,ticks=(t1,replace(t2,charge=1)))),N)
check(v.claim_universal_clock(),O)
check(v.physical_external('Ogami–Tajima v2 full thermodynamic-limit no-go'),O)
# Actual old H24 constructor and independent verifier; binds original input.
for n,C,expected in [(1,((1,),),0),(1,((1,),(-1,)),1),(0,((),),1),(2,((1,-2),(2,)),0)]:
    r=h.guarded_construct(n,C);check(r.result,Y);assert r.minimum_failed_clauses==expected and r.operational_clock.status==O
    assert r.source_belnap==((1,0) if expected==0 else (0,1))
    bad=list(r.proof.nodes); k=r.proof.root; bad[k]=replace(bad[k],m=bad[k].m+1)
    forged=h.guarded_return(n,C,replace(r.proof,nodes=tuple(bad)));check(forged.result,N);assert forged.source_belnap==(0,0)
# Counterexample to fixed-order residual DAG; check actual retained constructor sizes.
nodes=[]
for k in range(1,9):
    C=tuple(cl for j in range(1,k+1) for cl in ((-j,k+j),(j,-(k+j))))+tuple(cl for j in range(1,k) for cl in ((-(k+j),k+j+1),(k+j,-(k+j+1))))
    r=h.guarded_construct(2*k,C);check(r.result,Y);assert r.ground_count==2 and r.minimum_failed_clauses==0
    check(v.residual_expansion(k),N)
    # k=1 can use product reduction before a boundary; count bound 2^k still holds.
    assert len(r.proof.nodes)>=2**k
    nodes.append({'k':k,'nodes':len(r.proof.nodes),'lower_bound':2**k})
# Symmetry and odd-unit Haar, and distinction between wrapped position and a lift.
check(v.symmetric_input(v.SymmetryRequest(I,R,I[:,0])),Y)
check(v.symmetric_input(v.SymmetryRequest(I,R,I[:,1])),O)
check(v.six_frame_integral_haar(),N)
check(v.finite_observation_clock_alias(9,1),N)
check(v.empty_ground_from_reflection(),N)
# Recompute actual typed claims; forged, unrelated and open receipts cannot pass.
import operations as ops
cl=ops.Claim('winding',(9,1,(1,)*9)); proof=ops.prove(cl)
assert ops.accepts(cl,proof,Y)
assert not ops.accepts(ops.Claim('winding',(9,2,(1,)*9)),proof,Y)
assert not ops.accepts(cl,replace(proof,certificate=v.no('fake','fake','fake')),N)
openclaim=ops.Claim('claim_universal_clock',()); opened=ops.prove(openclaim)
assert ops.replay(openclaim,opened) and not ops.accepts(openclaim,opened,Y)
assert not ops.accepts(openclaim,opened,O)
assert ops.evaluate(ops.Claim('unknown_theorem',())).status==O
# Negative and positive rail evidence not collapsed.
assert v.combine((v.dyadic_zero_claim(8),v.claim_universal_clock()))==(0,1)
report={'checks':len(results),'status_counts':dict(Counter(r['status'] for r in results)), 'operations':sorted({r['operation'] for r in results}), 'actual_retained_residual_growth':nodes,'receipts':results,'scope':'exact finite certificates and written structural theorems, not a fresh Lean/Hets or continuum theorem replay'}
Path(__file__).with_name('receipts.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('checks','status_counts','operations','actual_retained_residual_growth')},indent=2))
