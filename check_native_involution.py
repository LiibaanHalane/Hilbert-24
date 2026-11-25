"""Exact arithmetic on the original sparse 4x4 native chart.
No uncomputed assignment-global norm is used as a primitive.
"""
from itertools import product
from random import Random
from pathlib import Path
import json

def eye(n=4): return [[int(i==j) for j in range(n)] for i in range(n)]
def zero(n=4): return [[0]*n for _ in range(n)]
def add(A,B,m): return [[(a+b)%m for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(a,A,m): return [[a*x%m for x in row] for row in A]
def sub(A,B,m): return add(A,scale(-1,B,m),m)
def mul(A,B,m): return [[sum(a*b for a,b in zip(x,y))%m for y in zip(*B)] for x in A]
def rho(t,b,p,h,r,k,m): return [[(t-2*b)%m,0,0,0],[0,p%m,h%m,0],[0,r%m,k%m,0],[b%m,0,0,t%m]]
def decode(A): return A[3][3],A[3][0],A[1][1],A[1][2],A[2][1],A[2][2]
def val(A,k): return min(((x&-x).bit_length()-1 if x else k) for row in A for x in (a%(1<<k) for a in row))
G=[[1,0,0,1],[0,2,-1,0],[0,-1,2,0],[1,0,0,2]]
GI3=[[6,0,0,-3],[0,2,1,0],[0,1,2,0],[-3,0,0,3]]
def dag(A,m):return mul(mul(scale(pow(3,-1,m),GI3,m),list(map(list,zip(*A))),m),G,m)
def normal(A,m): return scale(-pow(3,-1,m),add(A,scale(2,dag(A,m),m),m),m)
def inverse_normal(A,m):return sub(A,scale(2,dag(A,m),m),m)
def geom(X,k):
    m=1<<k; t=eye(); s=eye()
    for _ in range(1,k): t=mul(t,X,m); s=add(s,t,m)
    return s

def coef(base_exp,n,s,m):
    v=(n&-n).bit_length()-1; e=base_exp-s*v
    assert e>=0
    return (pow(2,e,m)*pow(pow(n>>v,s,m),-1,m))%m

def tau(A,k):
    m=1<<k; A2=mul(A,A,m); t=A; out=zero()
    for j in range((k+1)//2):
        c=pow(4,j,m)*(-1)**j*pow((2*j+1)**2,-1,m)%m
        out=add(out,scale(c,t,m),m);t=mul(t,A2,m)
    return out

def kappa(A,k):
    m=1<<k
    return mul(mul(A,geom(scale(-2,A,m),k),m),geom(scale(-6,A,m),k),m)
def land(A,k,log=False):
    """M=Li_2(16*kappa)/16; ell=log(1-16*kappa)/16 if log."""
    m=1<<k; X=kappa(A,k); t=X; out=zero()
    for n in range(1,(k+1)//2+1):
        c=coef(4*(n-1),n,1 if log else 2,m)
        out=add(out,scale(-c if log else c,t,m),m);t=mul(t,X,m)
    return out

def inv_chart(Y,k,fn=land):
    m=1<<k; X=Y
    for _ in range((k+1)//2): X=add(Y,sub(X,fn(X,k),m),m)
    return X

def inv_land(Y,k):
    m=1<<k; X=inv_chart(Y,k); ell=land(X,k,True)
    # Landen: M(-X)=-M(X)-8 ell(X)^2.
    return sub(scale(-1,Y,m),scale(8,mul(ell,ell,m),m),m)

def mark(u,m): return rho(0,0,u,0,0,u,m)
def anchors(u,m):return rho(1,0,u,0,0,u,m)
def reflection(u,m):
    """H-self-adjoint involution v=(1,u), H=[[2,-1],[-1,2]]."""
    d=pow((1-u+u*u)%m,-1,m)
    a=(2-u)*d%m; b=(-1+2*u)*d%m
    return rho(1,0,1-a,-b,-u*a,1-u*b,m)
def reflection_decode(A,m):
    assert A[1][2]%2==1
    return (A[2][2]-1)*pow(A[1][2],-1,m)%m

def main():
    rng=Random(20261125); counts={k:0 for k in ['chart_pairs','dagger_returns','landen_returns','involution_defects','clause_returns','reflection_returns','grade_branch_returns']}
    for k in [1,2,3,4,5,8,12,16,24,32]:
        m=1<<k
        for _ in range(16):
            A=rho(*[rng.randrange(m) for _ in range(6)],m)
            B=rho(*[rng.randrange(m) for _ in range(6)],m)
            # force many common-prefix pairs as well
            j=rng.randrange(k+1); B=add(A,scale(1<<j,B,m),m)
            for fn in [tau,land]:
                X,Y=fn(A,k),fn(B,k)
                assert rho(*decode(X),m)==X
                assert val(sub(X,Y,m),k)==val(sub(A,B,m),k)
                assert inv_chart(X,k,fn)==A
                counts['chart_pairs']+=1
                assert fn(dag(A,m),k)==dag(X,m);counts['dagger_returns']+=1
            X=land(A,k); Y=inv_land(X,k)
            assert Y==land(scale(-1,A,m),k)
            assert inv_land(Y,k)==X; counts['landen_returns']+=1
            assert inverse_normal(normal(A,m),m)==A
            # Guard digit: compute the displacement at k+1 before dividing by 2.
            M=2*m; Ag=rho(*decode(A),M); Xg=land(Ag,k+1)
            diff=sub(Xg,inv_land(Xg,k+1),M)
            assert all(x%2==0 for row in diff for x in row)
            half=[[x//2 for x in row] for row in diff]
            assert val(half,k)==val(A,k); counts['involution_defects']+=1
            fs=[rng.randrange(2) for _ in range(rng.randrange(25))]
            P=eye(); c=tau(eye(),k+1)[0][0]; M=2*m
            for f in fs:
                U=anchors(1-2*f,M)
                assert mul(U,U,M)==eye() and dag(U,M)==U
                assert tau(U,k+1)==scale(c,U,M)
                V=sub(scale(3*c,eye(),M),tau(U,k+1),M)
                assert all(x%2==0 for row in V for x in row)
                factor=scale(pow(c,-1,m),[[x//2 for x in row] for row in V],m)
                assert factor==anchors(1+f,m)
                P=mul(P,factor,m)
            assert P==anchors(pow(2,sum(fs),m),m);counts['clause_returns']+=1
            u=rng.randrange(m);v=rng.randrange(m)
            Ru,Rv=reflection(u,m),reflection(v,m)
            assert mul(Ru,Ru,m)==eye() and dag(Ru,m)==Ru
            assert reflection_decode(Ru,m)==u
            assert val(sub(Ru,Rv,m),k)==val(mark((u-v)%m,m),k)
            counts['reflection_returns']+=1
        for a,b in product(range(k+1),repeat=2):
            u,v=pow(2,a,m),pow(2,b,m)
            X=land(rho(0,0,u,0,0,v,m),k)
            swap=rho(1,0,0,1,1,0,m)
            assert mul(swap,swap,m)==eye() and dag(swap,m)==swap
            assert mul(mul(swap,X,m),swap,m)==land(rho(0,0,v,0,0,u,m),k)
            A=inv_chart(X,k)
            grades=[val(mark(z,m),k) for z in (A[1][1],A[2][2])]
            assert grades==[a,b]
            assert min(grades)==min(a,b)
            counts['grade_branch_returns']+=1
    print(json.dumps(counts,indent=2))
    Path(__file__).with_name('checks.json').write_text(json.dumps(counts,indent=2)+'\n')
if __name__=='__main__': main()
