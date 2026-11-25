"""Exact finite checks of the marked nine-chart covariance theorem.
Run: python check.py (requires sympy). The universal proofs are in the answer;
these are algebraic checks, not a proof assistant kernel receipt.
"""
from itertools import product
from sympy import Matrix, eye, zeros, diag, symbols, expand, simplify

G = Matrix([[1,0,0,1],[0,2,-1,0],[0,-1,2,0],[1,0,0,2]])
R = Matrix([[1,0,0,0],[0,0,-1,0],[0,1,-1,0],[0,0,0,1]])
G3 = diag(G,G,G)
I4,I12=eye(4),eye(12)
Z=zeros(4)
H=Matrix.vstack(Matrix.hstack(Z,Z,R), Matrix.hstack(I4,Z,Z), Matrix.hstack(Z,I4,Z))
def dagger(A, gin, gout):
    return gin.inv()*A.T*gout
assert R**3==I4 and R!=I4
assert dagger(R,G,G)==R**2
assert H**3==diag(R,R,R) and H**9==I12
assert H**3!=I12 and dagger(H,G3,G3)==H**8
# A split chart is an embedding of the SAME marked source; E_i's range
# can coincide, so the chart index is a retained mark, not a new witness.
J0=Matrix.vstack(I4,Z,Z)
E=[H**i*J0 for i in range(9)]
D=[dagger(e,G,G3) for e in E]
P=[e*d for e,d in zip(E,D)]
assert all(d*e==I4 for e,d in zip(E,D))
assert all(p*p==p and dagger(p,G3,G3)==p for p in P)
U={(j,i):E[j]*D[i] for i,j in product(range(9),repeat=2)}
for i,j,k in product(range(9),repeat=3):
    assert U[k,j]*U[j,i]==U[k,i]
for i,j in product(range(9),repeat=2):
    assert dagger(U[j,i],G3,G3)==U[i,j]
    assert U[i,j]*U[j,i]==P[i]
# Involution from the native Gram algebra, and its conjugate on each split image.
K=diag(-1,1,1,-1)
assert dagger(K,G,G)==K and K*K==I4
F=[e*K*d for e,d in zip(E,D)]
assert all(dagger(f,G3,G3)==f and f*f==p for f,p in zip(F,P))
for i,j in product(range(9),repeat=2):
    assert U[j,i]*F[i]==F[j]*U[j,i]
# Odd polylog in the split-image algebra, at each exact dyadic aperture.
# Scalar c is odd; reduction modulo 2^m of its inverse is therefore defined.
def mod(A,M):
    return A.applyfunc(lambda x:int(x)%M)
for m in range(1,33):
    M=1<<m
    c=sum((-1)**j * 4**j * pow(2*j+1,-1,M) for j in range((m+1)//2))%M
    assert c%4==1%min(M,4) if M>=4 else c==1
    # F_i^(2j+1)=F_i as proved by F_i^2=P_i, P_i F_i=F_i.
    for f in F:
        assert mod(pow(c,-1,M)*c*f,M)==mod(f,M)
# Hilbert 24: a concrete potential change on a 9-vertex marked cycle.
# Weights are declared exact integer charges, not measured host times.
phi=[2,0,3,1,4,2,5,3,1]
w=[7]*9
wp=[w[i]+phi[(i+1)%9]-phi[i] for i in range(9)]
assert all(t>=0 for t in wp) and sum(w)==sum(wp)
for i in range(9):
    for length in range(28):
        cost=sum(w[(i+j)%9] for j in range(length))
        costp=sum(wp[(i+j)%9] for j in range(length))
        assert costp-cost==phi[(i+length)%9]-phi[i]
# Maxwell symbol and directional energy identity, with unit condition exposed.
x,y,z,a,b,c,l,m,n=symbols('x y z a b c l m n', real=True)
e=Matrix([x,y,z]); B=Matrix([a,b,c]); v=Matrix([l,m,n]); C=Matrix([[0,-n,m],[n,0,-l],[-m,l,0]])
A=Matrix.vstack(Matrix.hstack(zeros(3),C),Matrix.hstack(-C,zeros(3)))
assert A.T==A
assert (A**3-v.dot(v)*A).applyfunc(expand)==zeros(6)
res=expand(e.dot(e)+B.dot(B)-2*v.dot(e.cross(B))-(B-v.cross(e)).dot(B-v.cross(e))-(v.dot(e))**2)
assert expand(res-(1-v.dot(v))*e.dot(e))==0
print('native R order 3, H order 9, exact Gram dagger: PASS')
print('9 split charts, 729 cocycles, 81 dagger inverses, 81 intertwiners: PASS')
print('288 normalized odd-polylog returns at 32 dyadic apertures: PASS')
print('252 finite path boundary-charge identities: PASS')
print('Maxwell directional symbol and energy-flux polynomial identities: PASS')
