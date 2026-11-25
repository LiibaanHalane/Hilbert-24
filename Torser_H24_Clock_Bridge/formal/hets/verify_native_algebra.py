"""Exact ordered-ring certificate for the new native clock bridge.

This is universal free-associative normalization, not finite SAT sampling.
The ring-normalization kernel is the unchanged archived implementation.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, json, shutil, sys

D=Path(__file__).resolve().parent
original=Path('/workspace/scratch/e609d6fab5c5/pnp_work/extracted/PNP_Multiple_Constructions/PNP_Multiple_Constructions/algebra')
dep=D/'deps/native_algebra';dep.mkdir(parents=True,exist_ok=True)
for name in ['inverse_limit_microcosm.py','noncommutative_native.py','torsor_matrix.py','canonical_core.py']:
    if original.exists():shutil.copyfile(original/name,dep/name)
sys.path.insert(0,str(dep))
from noncommutative_native import Polynomial as P, identity
import inverse_limit_microcosm as native
import torsor_matrix as frames

def star(x):
    x=P.cast(x)
    return P.make((tuple(v[:-1] if v.endswith('*') else v+'*' for v in reversed(word)),coefficient)
                  for word,coefficient in x.terms)
def transpose_star(a):return [[star(a[j][i]) for j in range(len(a))] for i in range(len(a[0]))]
def matrix(a):return [[P.cast(x) for x in r] for r in a]
def eye(n):return matrix([[int(i==j) for j in range(n)] for i in range(n)])
def mm(a,b):return native.mm(a,b)
def pack(p,w):return native.rho((p,0,p,w,0,p))
def clock(k):return native.rho((1,0,1,k,0,1))
J=matrix([[1,0,0,1],[0,2,-1,0],[0,-1,2,0],[1,0,0,2]])
JI=matrix([[2,0,0,-1],[0,Fraction(2,3),Fraction(1,3),0],
           [0,Fraction(1,3),Fraction(2,3),0],[-1,0,0,1]])
def dagger(a):return mm(JI,mm(transpose_star(a),J))

def main():
    proofs=[]
    a=tuple(P.variable('a'+str(i)) for i in range(6))
    b=tuple(P.variable('b'+str(i)) for i in range(6))
    c=tuple(P.variable('c'+str(i)) for i in range(6))
    proofs.append(identity('native_decoder',
                           [native.rho(a)[3][3],native.rho(a)[3][0],native.rho(a)[1][1],native.rho(a)[1][2],native.rho(a)[2][1],native.rho(a)[2][2]],a))
    proofs.append(identity('noncommutative_native_product',native.rho(native.native_product(a,b)),mm(native.rho(a),native.rho(b))))
    proofs.append(identity('noncommutative_native_associativity',native.native_product(native.native_product(a,b),c),native.native_product(a,native.native_product(b,c))))
    p,w,q,z=(P.variable(x) for x in ['P_f','W_fc','P_g','W_gd'])
    proofs.append(identity('weighted_context_clock_cocycle',mm(pack(q,z),pack(p,w)),pack(q*p,q*w+z*p)))
    k,l,phi,eta=(P.variable(x) for x in ['k','l','Phi_next','eta'])
    proofs.append(identity('clock_shear_addition',mm(clock(k),clock(l)),clock(k+l)))
    proofs.append(identity('upper_reserve_matrix',mm(clock(1),mm(clock(phi),clock(eta))),clock(1+phi+eta)))
    proofs.append(identity('clock_inverse_is_negative_shear',mm(clock(k),clock(-k)),eye(4)))
    proofs.append(identity('gram_inverse_left',mm(JI,J),eye(4)))
    proofs.append(identity('gram_inverse_right',mm(J,JI),eye(4)))
    X=native.rho(a);Y=native.rho(b)
    proofs.append(identity('gram_dagger_reverses_ordered_product',dagger(mm(X,Y)),mm(dagger(Y),dagger(X))))
    proofs.append(identity('gram_dagger_involutive',dagger(dagger(X)),X))
    G=matrix([[2,-1],[-1,2]]);GI=matrix([[Fraction(2,3),Fraction(1,3)],[Fraction(1,3),Fraction(2,3)]])
    mid=[[a[2],a[3]],[a[4],a[5]]]; md=mm(GI,mm(transpose_star(mid),G))
    proofs.append(identity('full_native_dagger_same_six_coordinates',dagger(X),native.rho((star(a[0]),star(a[1]),md[0][0],md[0][1],md[1][0],md[1][1]))))
    # The natural clock coordinate is self-adjoint, unlike a general coefficient.
    kk=star(k)
    expected=[[1+Fraction(2,3)*kk,-Fraction(1,3)*kk],[Fraction(4,3)*kk,1-Fraction(2,3)*kk]]
    proofs.append(identity('exact_clock_gram_adjoint',mm(GI,mm(transpose_star([[P.cast(1),k],[P.cast(0),P.cast(1)]]),G)),expected))
    frame_checks=[]
    for g in frames.NAMES:
        F=matrix(frames.MATRICES[g]);FI=matrix(frames.MATRICES[frames.inverse(g)])
        proofs.append(identity('frame_gram_unitary_'+g,dagger(F),FI))
        for h in frames.NAMES:
            H=matrix(frames.MATRICES[h]);HI=matrix(frames.MATRICES[frames.inverse(h)])
            proofs.append(identity('frame_product_'+g+'_'+h,mm(F,H),matrix(frames.MATRICES[frames.multiply(g,h)])))
            # Intermediate chart cancellation for arbitrary operator matrices.
            left=mm(mm(F,mm(Y,HI)),mm(H,mm(X,FI)))
            right=mm(F,mm(mm(Y,X),FI))
            proofs.append(identity('framed_clock_fusion_'+g+'_'+h,left,right))
            frame_checks.append([g,h])
    # A literal nonzero clock value proves the adjoint is not being called the inverse.
    clock_one_dagger=dagger(clock(P.cast(1)))
    assert any(clock_one_dagger[i][j] != P.cast(clock(-1)[i][j]) for i in range(4) for j in range(4))
    rows=[]
    for c0 in [0,1]:
        for a0 in [0,1]:
            for b0 in [0,1]:
                x=(c0,a0,b0)
                f=lambda x:(x[0],x[2],x[1]) if x[0] else x
                t=lambda x:(x[0],x[1],x[2]^(x[0]&x[1]))
                assert f(f(x))==x and t(t(x))==x
                rows.append({'input':x,'fredkin':f(x),'toffoli':t(x)})
    out={'method':'Exact normal forms in the free associative rational algebra; operator word order retained; rational denominators odd.',
         'universal_algebra_identities':proofs,'identity_count':len(proofs),'actual_fixed_frame_pair_count':len(frame_checks),
         'literal_three_bit_gate_table':rows,
         'clock_adjoint_distinct_from_time_inverse_at_one':True,
         'scope':'Closed native algebra, cost cocycle, frames and dagger; no arbitrary-CNF runtime or polynomial-envelope claim.',
         'formal_sha256':hashlib.sha256((D/'Native_Clock_Torser.het').read_bytes()).hexdigest()}
    (D/'checks/native-algebra-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'identities':len(proofs),'frame_pairs':len(frame_checks),'status':'all exact normal forms agree'}))
if __name__=='__main__':main()
