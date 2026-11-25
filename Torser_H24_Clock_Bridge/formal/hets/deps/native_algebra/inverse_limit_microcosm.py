"""Exact inverse-limit arithmetic and the retained minimal microcosm.

Q: What is the object as a canonical Collatz proof ball?
A: A finite constructor/proof prefix w specifies C_w = r_w + 2^k Z_2.
   Its basis-ball number is 2^k-1+r_w. The normalized Collatz map is
   T(2x)=x, T(2x+1)=3x+2, with inverse branches 2y and (2y-1)/3.
   B_w(y)=(2^k y-c_w)/3^h; T^k B_w(y)=y for EVERY 2-adic tail y.
   The code below uses that convention throughout. It does not replace it
   by the different map (3x+parity(x))/2 on the even sheet.

Q: How are all the components 2-adic?
A: Compatible residues modulo 2^m ARE a 2-adic point. Every operation below
   is defined at every finite demand and respects reduction to smaller m.
   Six coefficient streams interleave into one stream with exact lane
   inverses. This is a homeomorphism with transported operations, not an
   assertion that ordinary bit interleaving preserves ordinary multiplication.
   Finite syntax, source indices, proof references and Clifford tableaux are
   encoded by the existing self-delimiting constructor codec. Infinite tails
   remain fields. No finite call constructs or enumerates an infinite list.

Q: Where are the torser and tesseract?
A: canonical_core.Position is V x V*, V=F_2^2: sixteen incidence positions.
   Its six GL_2(F_2) frames act on v and contragrediently on the question.
   Its DEPENDENT payload contains source, proof, continuation and work.
   An incidence coordinate alone is not that entire equipped object.
   The coefficient algebra is Z_2[S_3], represented faithfully by the
   six-coordinate native image in 4x4 matrices constructed below.

Each finite residue returned here is exact, not a floating approximation.
The inverse limit is the compatible family of these exact projections.
An arbitrary supplied digit oracle has its own acquisition work; retaining
that oracle does not declare its future computation free.
"""
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

from canonical_core import Ball, inverse_odd_power_two


@dataclass(frozen=True,eq=False)
class Z2:
    op: str
    args: tuple[Any,...]

    @staticmethod
    def integer(value):
        if type(value) is not int:raise ValueError('an integer is required')
        return Z2('integer',(value,))

    @staticmethod
    def digits(producer):
        return Z2('digits',(producer,))

    def __add__(self,other):return Z2('add',(self,other))
    def __mul__(self,other):return Z2('multiply',(self,other))

    def residue(self,precision):
        if type(precision) is not int or precision<0:raise ValueError('a natural precision is required')
        # Explicit continuation stack: arbitrarily deep finite expressions do
        # not depend on the host's recursion limit. Memo keys include precision.
        memo={};agenda=[(False,self,precision)]
        while agenda:
            done,node,m=agenda.pop();key=(id(node),m)
            if key in memo:continue
            if m==0:memo[key]=0;continue
            a=node.args;op=node.op;mask=(1<<m)-1
            if op in ('add','multiply'):children=[(a[0],m),(a[1],m)]
            elif op in ('prefix','macro-prefix'):children=[(a[1],max(0,m-a[0].depth))]
            elif op=='iterate':children=[(a[0],m+a[1])]
            elif op=='interleave':children=[(p,max(0,(m+5-j)//6)) for j,p in enumerate(a)]
            elif op=='lane':children=[(a[0],6*(m-1)+a[1]+1)]
            else:children=[]
            if not done and children:
                agenda.append((True,node,m))
                agenda.extend((False,p,k) for p,k in reversed(children))
                continue
            get=lambda child,k:memo[id(child),k]
            if op=='integer':value=a[0]
            elif op=='digits':
                value=0
                for i in range(m):
                    digit=a[0](i)
                    if digit not in (0,1):raise ValueError('nonbinary digit oracle')
                    value|=int(digit)<<i
            elif op=='add':value=get(a[0],m)+get(a[1],m)
            elif op=='multiply':value=get(a[0],m)*get(a[1],m)
            elif op=='prefix':
                ball,tail=a
                value=((1<<ball.depth)*get(tail,max(0,m-ball.depth))-ball.offset)
                value*=inverse_odd_power_two(3**ball.odd_steps,m)
            elif op=='macro-prefix':
                ball,tail=a
                scale,offset=ball.affine(m)
                value=scale*get(tail,max(0,m-ball.depth))+offset
            elif op=='iterate':
                point,steps=a;value=get(point,m+steps)
                for _ in range(steps):value=(3*value+1)//2 if value&1 else value//2
            elif op=='interleave':
                values=[get(p,max(0,(m+5-j)//6)) for j,p in enumerate(a)]
                value=sum(((values[i%6]>>(i//6))&1)<<i for i in range(m))
            elif op=='lane':
                value=sum(((get(a[0],6*(m-1)+a[1]+1)>>(6*i+a[1]))&1)<<i for i in range(m))
            else:raise ValueError('unknown inverse-limit constructor')
            memo[key]=value&mask
        return memo[id(self),precision]


def prepend(word,tail):
    return Z2('prefix',(Ball.from_word(word),tail))


def iterate(point,steps):
    if type(steps) is not int or steps<0:raise ValueError('a natural iteration count is required')
    return Z2('iterate',(point,steps))


def parity_prefix(point,length):
    if type(length) is not int or length<0:raise ValueError('a natural word length is required')
    value=point.residue(length);out=[]
    for _ in range(length):
        bit=value&1;out.append(bit)
        value=(3*value+1)//2 if bit else value//2
    return tuple(out)


def interleave(lanes):
    if len(lanes)!=6:raise ValueError('the native coefficient chart has six lanes')
    return Z2('interleave',tuple(lanes))


def lane(point,index):
    if type(index) is not int or index not in range(6):raise ValueError('unknown native lane')
    return Z2('lane',(point,index))


@dataclass(frozen=True)
class PackedMany:
    point: Z2
    count: int
    levels: int

    def unpack(self,index):
        if type(index) is not int or not 0<=index<self.count:raise ValueError('unknown retained component')
        point=self.point
        for level in reversed(range(self.levels)):
            point=lane(point,(index//(6**level))%6)
        return point


def pack_many(points):
    # An arbitrary finite family is one point, with at most six ports per
    # node. Inverse cancellation at one node and induction on the tree give
    # unpack(pack_many(xs),i)=xs[i] at EVERY demanded precision.
    # For countably many lanes the same construction uses a bit pairing:
    # pair(i,j)=(i+j)(i+j+1)/2+j; packed_bit(pair(i,j))=lane_i.bit(j).
    # Each finite demand visits finitely many coordinates. The acquisition
    # work of those supplied coordinates is still part of the requested run.
    points=tuple(points)
    if not points:raise ValueError('use a declared empty record rather than an unindexed component')
    current=points;levels=0
    while len(current)>1:
        groups=[]
        for i in range(0,len(current),6):
            group=current[i:i+6]
            groups.append(interleave(group+(Z2.integer(0),)*(6-len(group))))
        current=tuple(groups);levels+=1
    return PackedMany(current[0],len(points),levels)


def _reduce(value,modulus):
    if modulus is None:return value
    return value&(modulus-1) if modulus>0 and modulus&(modulus-1)==0 else value%modulus


def divide_odd_constant(value,divisor,precision):
    # LSB long division with a bounded carry. Invariant after i digits:
    # divisor*q_low = value_low + 2^i*carry. For positive odd divisor,
    # 0<=carry<divisor. The input/output conversions and digit pass are
    # linear in precision for a FIXED divisor, here 3 or 63. No m-bit
    # multiplication by a separately computed inverse is required.
    if type(precision) is not int or precision<0 or type(divisor) is not int or divisor<=0 or divisor%2==0:
        raise ValueError('a positive odd divisor and natural aperture are required')
    count=(precision+7)//8
    raw=(value&((1<<precision)-1)).to_bytes(count,'little')
    out=bytearray(count);carry=0
    for i in range(precision):
        bit=(raw[i//8]>>(i%8))&1
        quotient=(bit-carry)&1
        out[i//8]|=quotient<<(i%8)
        carry=(carry+divisor*quotient-bit)//2
    return int.from_bytes(out,'little')


def mm(a,b,modulus=None):
    return tuple(tuple(_reduce(sum(a[i][k]*b[k][j] for k in range(len(b))),modulus)
                       for j in range(len(b[0]))) for i in range(len(a)))


def native_product(a,b,precision=None):
    modulus=None if precision is None else 1<<precision;t,c,*x=a;u,d,*y=b
    z=mm((x[:2],x[2:]),(y[:2],y[2:]),modulus)
    return (_reduce(t*u,modulus),_reduce(t*d+c*u-2*c*d,modulus),*z[0],*z[1])


def rho(a,precision=None):
    modulus=None if precision is None else 1<<precision
    t,b,x,y,z,w=(_reduce(v,modulus) for v in a)
    return ((_reduce(t-2*b,modulus),0,0,0),(0,x,y,0),(0,z,w,0),(b,0,0,t))


def delta(matrix,precision):
    a=(matrix[3][3],matrix[3][0],matrix[1][1],matrix[1][2],matrix[2][1],matrix[2][2])
    normalized=tuple(tuple(v% (1<<precision) for v in row) for row in matrix)
    if rho(a,precision)!=normalized:raise ValueError('matrix is outside the registered native image')
    return a


def dagger(a,precision=None):
    # Integral A2 invariant form J, determinant 3 (a 2-adic unit).
    # D(B)=J^-1 B^t J, so D^2=1 and D(BC)=D(C)D(B).
    modulus=None if precision is None else 1<<precision
    t,b,x,y,z,w=a
    J=((2,-1),(-1,2));numerators=mm(mm(((2,1),(1,2)),((x,z),(y,w))),J)
    if precision is None:out=tuple(tuple(v*Fraction(1,3) for v in row) for row in numerators)
    else:out=tuple(tuple(divide_odd_constant(v,3,precision) for v in row) for row in numerators)
    return (_reduce(t,modulus),_reduce(b,modulus),*out[0],*out[1])


def braid(seeds,precision=None):
    if len(seeds)!=6 or any(len(x)!=6 for x in seeds):raise ValueError('six native-algebra seeds are required')
    return tuple(dagger(seeds[(i-1)%6],precision) for i in range(6))


def six_fixed_point(seeds,precision=None):
    """F_B(X)=B+2UX; U^6=1; exact solution -sum(2^j U^j B)/63."""
    if precision is not None and (type(precision) is not int or precision<0):raise ValueError('a natural aperture is required')
    modulus=None if precision is None else 1<<precision
    terms=tuple(tuple(_reduce(x,modulus) for x in row) for row in seeds)
    if len(terms)!=6 or any(len(row)!=6 for row in terms):raise ValueError('six seeds of rank six are required')
    total=[[0]*6 for _ in range(6)]
    for j in range(6):
        for i in range(6):
            for k in range(6):total[i][k]=_reduce(total[i][k]+(1<<j)*terms[i][k],modulus)
        terms=braid(terms,precision)
    if precision is None:return tuple(tuple(-x*Fraction(1,63) for x in row) for row in total)
    return tuple(tuple(divide_odd_constant(-x,63,precision) for x in row) for row in total)
