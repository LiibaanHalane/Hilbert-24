"""H24 clock invariant operations. Exact finite checks, not a universal theorem oracle.
Python 3.10+ and sympy. All checkers fail closed on unsupported coefficients.
PROVED/REFUTED concern the named judgement at its stated scope, OPEN is neither.
"""
from dataclasses import dataclass, asdict
from enum import Enum
from fractions import Fraction as Q
from pathlib import Path
from typing import Any, Callable
import sys
import sympy as s

class Status(str, Enum):
    PROVED='PROVED'; REFUTED='REFUTED'; OPEN='OPEN'
@dataclass(frozen=True)
class Receipt:
    operation: str
    scope: str
    status: Status
    evidence: tuple[str,...]
    @property
    def belnap(self): return (int(self.status==Status.PROVED),int(self.status==Status.REFUTED))
    def json(self): return dict(asdict(self),status=self.status.value,belnap=self.belnap)
def receipt(op,scope,st,*ev): return Receipt(op,scope,st,tuple(map(str,ev)))
def yes(op,scope,*ev): return receipt(op,scope,Status.PROVED,*ev)
def no(op,scope,*ev): return receipt(op,scope,Status.REFUTED,*ev)
def opn(op,scope,*ev): return receipt(op,scope,Status.OPEN,*ev)

G=s.Matrix([[1,0,0,1],[0,2,-1,0],[0,-1,2,0],[1,0,0,2]])
R=s.Matrix([[1,0,0,0],[0,0,-1,0],[0,1,-1,0],[0,0,0,1]])
S=s.Matrix([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
I4=s.eye(4)

def exact(A):
    """Only Gaussian rational entries, so equality and sign tests terminate."""
    M=s.Matrix(A)
    if any(not (s.re(x).is_Rational and s.im(x).is_Rational) for x in M):
        raise ValueError('exact Gaussian rational coefficients required')
    return M

def posmetric(G):
    G=exact(G)
    if G.rows!=G.cols or G!=G.conjugate().T or not all(G[:i,:i].det()>0 for i in range(1,G.rows+1)):
        raise ValueError('positive definite Gram metric required')
    return G

def dag(A,Gsrc,Gdst=None):
    return Gsrc.inv()*A.conjugate().T*(Gsrc if Gdst is None else Gdst)

def first(A):
    for i in range(A.rows):
        for j in range(A.cols):
            if A[i,j]!=0:return (i,j,A[i,j])
    return None

@dataclass(frozen=True)
class ModeRequest:
    A: Any; D: Any; B: Any; G: Any; x: Any; omega: Any

def persistent_mode(r: ModeRequest):
    """Finite positive-metric no-go: no dissipative contribution to a pure imaginary mode.
    B is a certified square factor D=-B†B. No positivity inference from dyadic squares."""
    op='CLOCK.DISSIPATION_FREE_MODE'; scope='finite positive Gram; given nonzero eigenmode'
    try:
        G0=posmetric(r.G); A,D,B,x=map(exact,(r.A,r.D,r.B,r.x)); w=s.sympify(r.omega)
        d=G0.rows
        if A.shape!=(d,d) or D.shape!=(d,d) or B.cols!=d or x.shape!=(d,1) or not w.is_Rational: raise ValueError('shape/frequency')
        if A+dag(A,G0)!=s.zeros(d): return opn(op,scope,'skew-adjoint premise fails')
        if D!=-dag(B,G0,s.eye(B.rows))*B:return opn(op,scope,'negative square factor premise fails')
        if x==s.zeros(d,1):return opn(op,scope,'zero is not a clock mode')
        E=(A+D)*x-s.I*w*x
        if E!=s.zeros(d,1):return no(op,scope,'claimed mode fails',first(E))
        if B*x!=s.zeros(B.rows,1) or D*x!=s.zeros(d,1) or A*x!=s.I*w*x:
            raise ArithmeticError('internal theorem contradiction')
        return yes(op,scope,'Bx=0','Dx=0','Ax=iωx',f'ω={w}')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

@dataclass(frozen=True)
class StationaryRequest:
    K: Any; rho: Any; O: Any; G: Any

def stationary_observation(r: StationaryRequest):
    op='CLOCK.STATIONARY_ONE_EVENT'; scope='finite Hamiltonian evolution; stationary density; fixed observable'
    try:
        g=posmetric(r.G); K,rho,O=map(exact,(r.K,r.rho,r.O)); d=g.rows
        if any(M.shape!=(d,d) for M in (K,rho,O)):raise ValueError('shape')
        if K!=dag(K,g) or rho!=dag(rho,g) or s.trace(rho)!=1:return opn(op,scope,'Hamiltonian/density premise fails')
        # PSD is checked through all principal minors (finite exact algebra).
        from itertools import combinations
        herm=g*rho
        if any(herm.extract(ii,ii).det()<0 for k in range(1,d+1) for ii in combinations(range(d),k)):
            return opn(op,scope,'density positivity fails')
        if K*rho!=rho*K:return no(op,scope,'stationarity fails',first(K*rho-rho*K))
        # Trace cyclicity and commutation prove tr(rho U† O U)=tr(rho O) for all t.
        deriv=s.trace(rho*(K*O-O*K))
        if deriv!=0:raise ArithmeticError('trace inconsistency')
        return yes(op,scope,'[K,rho]=0',f'constant={s.trace(rho*O)}','two-event correlations not constrained to be constant')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

@dataclass(frozen=True)
class HistoryRequest:
    transitions: tuple[Any,...]; initial: Any; G: Any

def history(r: HistoryRequest):
    op='CLOCK.HOLONOMY_SECTION'; scope='finite cycle; initial marked vector; Gram-isometric transitions'
    try:
        g=posmetric(r.G); d=g.rows; x=exact(r.initial); us=tuple(exact(u) for u in r.transitions)
        if not us or x.shape!=(d,1) or x==s.zeros(d,1):return opn(op,scope,'nonempty cycle and nonzero initial vector required')
        if any(u.shape!=(d,d) or dag(u,g)*u!=s.eye(d) for u in us):return opn(op,scope,'transition isometry premise fails')
        states=[x]
        for u in us:states.append(u*states[-1])
        seam=states[-1]-x
        if seam!=s.zeros(d,1):return no(op,scope,'closure seam',first(seam))
        return yes(op,scope,'zero energy at every seam',f'{len(us)} positions',f'initial={list(x)}')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

@dataclass(frozen=True)
class CovarianceRequest:
    U: Any; F: Any; Fp: Any; G: Any

def covariance(r: CovarianceRequest):
    op='TRANSPORT.COVARIANCE'; scope='exact finite Gram operators'
    try:
        g=posmetric(r.G); U,F,Fp=map(exact,(r.U,r.F,r.Fp)); d=g.rows
        if any(M.shape!=(d,d) for M in (U,F,Fp)):raise ValueError('shape')
        if dag(U,g)*U!=s.eye(d):return opn(op,scope,'Gram isometry premise fails')
        E=U*F-Fp*U
        if E!=s.zeros(d):return no(op,scope,'noncommuting entry (row,basis column,value)',first(E))
        return yes(op,scope,'UF=F′U','does not certify equality of work')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def locality(U,radius):
    op='CLOCK.STRICT_LOCALITY'; scope='one linear update on a line; matrix support'
    try:
        U=exact(U)
        if U.rows!=U.cols or type(radius)!=int or radius<0:raise ValueError('square matrix and nonnegative radius required')
        for i in range(U.rows):
            for j in range(U.cols):
                if abs(i-j)>radius and U[i,j]!=0:return no(op,scope,'outside causal stencil',(i,j,U[i,j]))
        return yes(op,scope,f'radius={radius}')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def winding(N,w,steps):
    op='CLOCK.WINDING_MINIMUM'; scope='unit-cost adjacent signed steps in lifted cycle'
    if type(N)!=int or N<3 or type(w)!=int or any(type(j)!=int or j not in (-1,1) for j in steps):return opn(op,scope,'invalid lift')
    if sum(steps)!=N*w:return no(op,scope,'wrong lifted endpoint',sum(steps),N*w)
    if len(steps)!=N*abs(w):return no(op,scope,'nonminimal route',len(steps),N*abs(w))
    return yes(op,scope,f'minimum={N*abs(w)}','|sum steps| ≤ number of steps; constant-sign path attains')

def winding_alias(N,w,v):
    op='CLOCK.WRAPPED_READOUT_INJECTIVE'; scope='uniform Nth-root samples of z^w'
    if type(N)!=int or N<1 or type(w)!=int or type(v)!=int:return opn(op,scope,'invalid integer input')
    if w!=v and (w-v)%N==0:return no(op,scope,f'w={w}, v={v}',f'identical at all {N} samples; distinct lifts')
    if w==v:return opn(op,scope,'comparison must use distinct lifts')
    return yes(op,scope,'distinct for this pair at primitive root','not a global injectivity theorem')

def scale_identification(length_scale,time_scale):
    op='CLOCK.DIMENSIONAL_SPEED_FROM_UNSCALED_LAWS'; scope='positive rescalings of length and additive response'
    a,b=Q(length_scale),Q(time_scale)
    if a<=0 or b<=0:return opn(op,scope,'positive scales required')
    if a!=b:return no(op,scope,'same additive laws, different rate',f'factor={a/b}')
    return opn(op,scope,'this rescaling does not distinguish the rates; no dimensional calibration supplied')

def gap_claim(depth,uniform_floor):
    """A constructive counterexample from Δ(3^d)<=4π²/9^d<40/9^d (π²<10)."""
    op='CLOCK.UNIFORM_CYCLE_GAP'; scope='unit-weight history Laplacian, N=3^d, trivial holonomy'
    if type(depth)!=int or depth<1:return opn(op,scope,'depth must be positive')
    f=Q(uniform_floor)
    if f<=0:return opn(op,scope,'strictly positive proposed floor required')
    # use bound π<22/7 ⇒ 4π²<40, not a floating point test
    ub=Q(40,9**depth)
    if ub<f:return no(op,scope,f'depth={depth}',f'Δ<={ub}<claimed {f}')
    return opn(op,scope,f'upper bound {ub} does not refute this floor at this depth')

def uniform_gap_counterexample(floor):
    f=Q(floor)
    if f<=0:return gap_claim(1,f)
    d=1
    while Q(40,9**d)>=f:d+=1
    return gap_claim(d,f)

def finite_clock_ccr(Qop,Pop,G0):
    op='CLOCK.EXACT_FINITE_CANONICAL_COMMUTATOR'; scope='positive-dimensional finite matrix; [Q,P]=iI'
    try:
        g=posmetric(G0); Qop,Pop=map(exact,(Qop,Pop)); d=g.rows
        if not d or Qop.shape!=(d,d) or Pop.shape!=(d,d):raise ValueError('shape')
        if s.trace(Qop*Pop-Pop*Qop)!=0:raise ArithmeticError('trace inconsistency')
        return no(op,scope,f'tr(commutator)=0, tr(iI)={s.I*d}')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def dyadic_zero_claim(k):
    op='PROOF.FINITE_APERTURE_IMPLIES_GLOBAL_ZERO'; scope='Z2 reduction at one finite cut'
    if type(k)!=int or k<1:return opn(op,scope,'positive cut required')
    return no(op,scope,f'0 and 2^{k} have identical residue but differ globally')

def dyadic_gram_claim(k):
    op='PROOF.DYADIC_SUM_SQUARES_FAITHFUL'; scope='finite residue ring; nontrivial vector'
    if type(k)!=int or k<2:return opn(op,scope,'k>=2 required for this fixture')
    x=1<<((k+1)//2); assert x%(1<<k) and x*x%(1<<k)==0
    return no(op,scope,f'x={x} nonzero mod 2^{k}, x²=0 mod 2^{k}')

def projector_involution(P,G0):
    op='PROOF.PROJECTOR_IS_SELF_INVERSE'; scope='explicit finite Gram projector'
    try:
        g=posmetric(G0); P=exact(P); d=g.rows
        if P.shape!=(d,d) or P*P!=P or dag(P,g)!=P:return opn(op,scope,'projector premise fails')
        if P!=s.eye(d):return no(op,scope,'idempotent and involutive implies identity',first(P-s.eye(d)))
        return yes(op,scope,'P=I')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def posterior(weights,likelihoods):
    op='EVIDENCE.BAYES_NORMALIZER'; scope='finite exact nonnegative weights with marks'
    w=tuple(map(Q,weights)); l=tuple(map(Q,likelihoods))
    if len(w)!=len(l) or any(x<0 for x in w+l):return opn(op,scope,'invalid weights/likelihoods')
    z=sum(a*b for a,b in zip(w,l))
    if not z:return no(op,scope,'zero total mass; conditioning undefined')
    return yes(op,scope,f'normalizer={z}',tuple(str(a*b/z) for a,b in zip(w,l)))

def independent_evidence_claim():
    op='EVIDENCE.MARGINALS_DETERMINE_JOINT'; scope='two Boolean clause evidence events'
    # x and x vs x and not x, uniform x; all marginals 1/2, joints 1/2 and 0
    return no(op,scope,'same marginals (1/2,1/2)','joint (x,x)=1/2; joint (x,not x)=0')

def moment_sufficiency_claim():
    op='EVIDENCE.THREE_MOMENTS_DETERMINE_GROUND'; scope='fixed q=2/3, nonnegative integer histograms'
    a=(8,12,186,0,279,0,27); b=(0,72,0,305,0,135,0)
    q=Q(2,3)
    def mom(h):return tuple(sum(Q(c)*q**j*j**k for j,c in enumerate(h)) for k in range(3))
    assert sum(a)==sum(b) and mom(a)==mom(b) and a[0]>0 and b[0]==0
    return no(op,scope,f'moments={mom(a)}',f'ground counts {a[0]}, {b[0]}','histogram witnesses; no general compression theorem inferred')

def residual_expansion(k):
    op='PROOF.FIXED_ORDER_POLYNOMIAL_CONTRACTION'; scope='connected equality-chain CNF; explicit normalized residual DAG, x-first'
    if type(k)!=int or k<1:return opn(op,scope,'positive k required')
    # proof: linear coeff of y_i differs by ±2 on differing prefix, y-chain stays connected.
    return no(op,scope,f'input family has {2*k} variables, {4*k-2} clauses',f'distinct residuals at x-prefix boundary = 2^{k}', 'family refutes uniform polynomial bound for this exact enumeration policy; not all algorithms')

@dataclass(frozen=True)
class Tick:
    before: str; after: str; charge: int; reserve_before: int; reserve_after: int; kind: str
@dataclass(frozen=True)
class TraceRequest:
    initial: str; ticks: tuple[Tick,...]; terminal: str; initial_budget: int
    # Actual finite transition table; model-specific declared unit bit step or cost.
    transitions: tuple[tuple[str,str,int,str],...]; checked_terminals: tuple[str,...]

def check_trace(r: TraceRequest):
    op='H24.PAID_TRACE'; scope='explicit finite transition system and declared charges; no universal runtime inference'
    if type(r.initial_budget)!=int or r.initial_budget<0:return opn(op,scope,'natural budget required')
    state=r.initial; reserve=r.initial_budget; total=0
    for t in r.ticks:
        if state in r.checked_terminals:return no(op,scope,'live action after terminal',state)
        if (t.before,t.after,t.charge,t.kind) not in r.transitions:return no(op,scope,'transition not admitted',t)
        if any(type(x)!=int for x in (t.charge,t.reserve_before,t.reserve_after)) or t.charge<1 or t.reserve_after<0:return no(op,scope,'invalid paid live step',t)
        if t.before!=state or t.reserve_before!=reserve or t.charge+t.reserve_after>reserve:return no(op,scope,'unpaid or disconnected step',t)
        state=t.after; reserve=t.reserve_after; total+=t.charge
    if state!=r.terminal or state not in r.checked_terminals:return no(op,scope,'no checked terminal in supplied finite semantics',state)
    if total+reserve>r.initial_budget:raise ArithmeticError('telescoping invariant broken')
    return yes(op,scope,f'work={total}',f'initial={r.initial_budget}',f'remaining={reserve}')

def claim_universal_clock():
    return opn('H24.UNIFORM_ORIGINAL_BIT_CLOCK','all original input lengths, one fixed implementation','requires source theorem of uniform coverage, actual bit-work accounting, and terminal soundness; finite samples cannot discharge')

def physical_external(name):
    return opn('PHYSICS.EXTERNAL_THEOREM','original physical/thermodynamic-limit model',name,'requires authenticated source proof and exact model binding, not a Boolean token')

def combine(receipts):
    """Conjunction in Belnap truth order; separate negative evidence. Not an auth mechanism."""
    rs=tuple(receipts)
    return int(all(r.belnap[0] for r in rs)),int(any(r.belnap[1] for r in rs))

def replay(operation:Callable, request, certificate:Receipt):
    return operation(request)==certificate

# Further clock/evidence guards from the same marked calculus.
def finite_perfect_clock(dim,positions):
    op='CLOCK.ORTHOGONAL_READOUT_CAPACITY'; scope='finite Hilbert space; perfectly distinguishable pure clock states'
    if type(dim)!=int or type(positions)!=int or dim<1 or positions<1:return opn(op,scope,'positive integer dimensions required')
    if positions>dim:return no(op,scope,f'{positions} mutually orthogonal nonzero states cannot fit in dimension {dim}')
    return yes(op,scope,'dimension obstruction absent; coordinate basis gives a witness','not a certificate of a specified device')

def two_level_orthogonal(p,z):
    op='CLOCK.TWO_LEVEL_ORTHOGONALIZATION'; scope='two energy eigenlevels; pure state; phase z on the complex unit circle'
    try:
        p=s.sympify(p); z=s.sympify(z)
        if not p.is_Rational or not 0<=p<=1 or not (s.re(z).is_Rational and s.im(z).is_Rational) or z*s.conjugate(z)!=1:return opn(op,scope,'exact population and unit phase required')
        amp=1-p+p*z
        if amp!=0:return no(op,scope,f'overlap={amp}',f'mean energy fraction={p}')
        if p!=s.Rational(1,2) or z!=-1:raise ArithmeticError('orthogonalization identity')
        return yes(op,scope,'p=1/2 and z=-1','first positive orthogonalizing phase π; E*T=πħ/2 for fixed gap and Schrödinger law')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

@dataclass(frozen=True)
class FluxRequest:
    E: Any; B: Any; n: Any

def vacuum_flux(r:FluxRequest):
    op='CLOCK.MAXWELL_ENERGY_FLUX'; scope='normalized real classical vacuum; unit direction; local field'
    try:
        E,B,n=map(exact,(r.E,r.B,r.n))
        if any(x.shape!=(3,1) or any(s.im(t)!=0 for t in x) for x in (E,B,n)) or n.dot(n)!=1:return opn(op,scope,'real triples and unit direction required')
        u=(E.dot(E)+B.dot(B))/2; flux=n.dot(E.cross(B)); v=B-n.cross(E)
        residual=(v.dot(v)+n.dot(E)**2)/2
        if u-flux!=residual or residual<0:raise ArithmeticError('energy identity')
        return yes(op,scope,f'u={u}',f'directed flux={flux}',f'nonnegative residual={residual}',f'saturates={residual==0}')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def classical_energy_floor(E,B,floor):
    op='CLOCK.POSITIVE_CLASSICAL_VACUUM_FLOOR'; scope='unconstrained classical vacuum amplitudes; no fixed signal flux'
    try:
        E,B=map(exact,(E,B)); f=s.sympify(floor)
        if E.shape!=(3,1) or B.shape!=(3,1) or any(s.im(t)!=0 for t in list(E)+list(B)) or not f.is_Rational or f<=0:return opn(op,scope,'real field triples and positive rational floor required')
        u=(E.dot(E)+B.dot(B))/2
        if u==0:return opn(op,scope,'need a nonzero field to scale')
        k=1
        while u/4**k>=f:k+=1
        return no(op,scope,f'amplitude scale=2^(-{k})',f'positive energy={u/4**k}<floor {f}', 'fixed-flux and quantum constraints not addressed')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def boundary_charge(edges,phi):
    op='H24.WORK_BOUNDARY_COVARIANCE'; scope='explicit finite directed edges with two nonnegative charges'
    for a,b,w,v in edges:
        if type(w)!=int or type(v)!=int or min(w,v)<0 or a not in phi or b not in phi:return opn(op,scope,'invalid edge data')
        if v-w!=phi[b]-phi[a]:return no(op,scope,'coboundary residual',(a,b,v-w-(phi[b]-phi[a])))
    return yes(op,scope,'all edge charge differences are exact potential differences','closed paths preserve charge; open paths retain endpoint term')

def clock_no_hit(prefix):
    op='H24.FINITE_NO_HIT_IMPLIES_NEVER'; scope='unrestricted binary first-hit streams'
    if any(type(b)!=int or b not in (0,1) for b in prefix) or any(prefix):return opn(op,scope,'prefix must be all-zero bits')
    return no(op,scope,f'common prefix length={len(prefix)}','extensions 0^∞ and 10^∞ after prefix disagree about eventual hit')

def bool_diagonal():
    op='PROOF.UNRESTRICTED_BOOLEAN_DIAGONAL_NAMING'; scope='total naming of all maps A→Bool by evaluation A×A→Bool'
    # names would name g(x)=not eval(x,x); substitution forces Boolean fixed point.
    return no(op,scope,'diagonal g(x)=not eval(x,x)','at a name for g: b=not b; both Boolean values refute it')

def no_work_from_identity():
    op='H24.SEMANTIC_IDENTITY_IMPLIES_ZERO_WORK'; scope='explicit two-step reversible identity circuit'
    return no(op,scope,'two bit flips implement identity','declared local work=2; doing nothing work=0','cost reduction requires an admitted equivalence and paid acquisition')

def haar_owner_integral(owners,boundary=0):
    """owners=(unique mark, depth, charge); normalized real Haar mass 2^-depth."""
    op='H24.FIRST_OWNER_WORK'; scope='finite acquired owner ledger; exact rational Haar integral'
    marks=set(); work=Q(boundary); density_integral=Q(boundary)
    if type(boundary)!=int or boundary<0:return opn(op,scope,'invalid boundary work')
    for mark,k,c in owners:
        if mark in marks:return no(op,scope,'duplicate first owner',mark)
        if type(k)!=int or type(c)!=int or min(k,c)<0:return opn(op,scope,'invalid depth or charge')
        marks.add(mark); p=Q(1,2**k); density_integral+=(Q(c)/p)*p; work+=c
    if density_integral!=work:raise ArithmeticError('owner integral')
    return yes(op,scope,f'work={work}',f'owners={len(marks)}','repeat references require separate actual charges')

@dataclass(frozen=True)
class SymmetryRequest:
    channel: Any; symmetry: Any; invariant_input: Any

def symmetric_input(r:SymmetryRequest):
    """A covariant linear channel cannot create asymmetry from an invariant input.
    No assertion that an arbitrary linear channel is CPTP, or that correlations are constant.
    """
    op='CLOCK.COVARIANT_INPUT_SYMMETRY'; scope='finite exact linear state/observable space, one specified symmetry'
    try:
        T,U,x=map(exact,(r.channel,r.symmetry,r.invariant_input)); d=T.rows
        if T.shape!=(d,d) or U.shape!=(d,d) or x.shape!=(d,1):raise ValueError('shape')
        if T*U!=U*T:return opn(op,scope,'covariance premise fails')
        if U*x!=x:return opn(op,scope,'input symmetry premise fails')
        if U*T*x!=T*x:raise ArithmeticError('covariance contradiction')
        return yes(op,scope,'U T x = T U x = T x','no new asymmetry in this state; no claim about two-event correlations')
    except (ValueError,TypeError) as e:return opn(op,scope,e)

def six_frame_integral_haar():
    """Native order-three versus order-six Haar in the ORIGINAL S3 chart."""
    op='PROOF.FULL_SIX_HAAR_INTEGRAL_OVER_Z2'; scope='normalized group average in the original native faithful S3 representation'
    T=s.Matrix([[-1,0,0,0],[0,0,1,0],[0,1,0,0],[1,0,0,1]])
    assert R**3==I4 and T*T==I4 and T*R*T==R**2 and dag(T,G)==T
    P3=(I4+R+R**2)/3
    P6=(I4+R+R**2+T+R*T+R**2*T)/6
    assert P3*P3==P3 and P6*P6==P6 and P6[3,0]==s.Rational(1,2)
    return no(op,scope,'C3 average is integral (3 is a unit)','S3 average has native entry b=1/2, not in Z2','use rational Haar or retain undivided sum')

def finite_observation_clock_alias(N,j):
    op='CLOCK.PERIODIC_POSITION_IS_UNWRAPPED_TIME'; scope='position observation on a finite cycle, no lifted winding mark'
    if type(N)!=int or N<1 or type(j)!=int:return opn(op,scope,'positive period and integer position required')
    return no(op,scope,f'two distinct lifted positions {j} and {j+N}',f'same residue {j%N}')

def empty_ground_from_reflection():
    op='PROOF.SELF_ADJOINT_INVOLUTION_IMPLIES_NONZERO_FIXED_WITNESS'; scope='positive real original native four-dimensional Gram space'
    A=-I4
    assert dag(A,G)==A and A*A==I4 and (A-I4).det()!=0
    return no(op,scope,'A=-I, A†=A=A^-1','Fix(A)={0}; no nonzero witness')
