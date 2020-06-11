//X_0(57). 
 //The space of ann. diffs. of trace zero. seems to have dimension 3 rather than 4 as we would expect. Okay, but we shouldn't actually care about these at all right?
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(57,19); //Just a few seconds.
X;
assert Genus(X) eq 5;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
rows:=[[&+[RowSequence(a)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]] : a in al] ;
w3:=iso<X->X | rows[1],rows[1]>; 
w19:=iso<X->X | rows[2], rows[2]>; 
w57:=iso<X->X | rows[3] , rows[3]>; //These are the Atkin-Lehner involutions.
assert w57 eq w3*w19; //Sanity check

cusps:=[X![1,0,0,0,0],X![1,1,0,1,0],X![3,3,1,2,1],X![3,9/2,-1/2,7/2,1]]; 
assert &and[1/j(cusp) eq 0 : cusp in cusps]; //We have found the four cusps.
assert {w(cusps[1]) : w in [w3*w3,w3,w19,w57]} eq Seqset(cusps);
Dtors:=[Divisor(cusps[i])-Divisor(cusps[1]) : i in [2,3,4]];
assert &and[not IsPrincipal(Dtor) : Dtor in Dtors]; //Sanity check
assert &and[IsPrincipal(6*Dtors[1]), not IsPrincipal(3*Dtors[1]), not IsPrincipal(2*Dtors[1])]; //Dtors[1] has order 6
assert &and([IsPrincipal(30*Dtors[2])] cat [not IsPrincipal(m*Dtors[2]) : m in Divisors(30) | not m eq 30]); //Dtors[2] has order 30
assert IsPrincipal(Dtors[1]+11*Dtors[2]-Dtors[3]); //Dtors[3] is in <Dtors[1],Dtors[2]>;
assert &and([not IsPrincipal(Dtors[1]-k*Dtors[2]) : k in [5,25]] cat [not IsPrincipal(2*Dtors[1]-k*Dtors[2]) : k in [10,20]] cat [not IsPrincipal(3*Dtors[1] - 15*Dtors[2])]);
//The latter shows that <Dtors[1]> and <Dtors[2]> have intersection {0} so J_0(57)(\Q)_{tors} \simeq Z/6Z x Z/30Z.


// We use an algorithm due to Stoll to find a generator for the free part of the  MW group of J(X/<w57>). We then lift it to J(X) to obtain a generator of an atmost index two subgroup of J(Q)/J(Q)_tors
CG2,projCG2:=CurveQuotient(AutomorphismGroup(X,[w57]));
SC, simplifier := SimplifiedModel(CG2);
J := Jacobian(SC);
P := SC![1,1,0] - SC![1,-1,0];
LogarithmicBound := Height(P) + HeightConstant(J);  // Bound on the naive h(Q)
AbsoluteBound := Ceiling(Exp(LogarithmicBound));
PtsUpToAbsBound := Points(J : Bound:=AbsoluteBound );
Redbase := ReducedBasis( [ pt : pt in PtsUpToAbsBound ]);
Jtors, maptoJ := TorsionSubgroup(J);
assert Redbase[1] in { pt + maptoJ(T) : T in Jtors, pt in {-P,P} }; // This asserts P generates J/J_tors
C2 := (simplifier^-1)(SC![1,1,0]);
C1 := (simplifier^-1)(SC![1,-1,0]);
D1 := Pullback(projCG2, Place(C2) -Place(C1)); // taking the pullback, we obtain an element which generates a subgroup of index at most 2 in J_0(57)
RR:=PolynomialRing(Rationals());
K<r>:=NumberField(RR![1,2,3]);
PP:= X(K)![-r+1,-4*r+1,r,-2*r+1,1];
assert D1 eq Place(cusps[2])+Place(cusps[4])-Place(PP);

// To be consistant with the rest of our code, we need the following quotient of X
C,projC:=CurveQuotient(AutomorphismGroup(X,[w3,w19]));


//We check the claimed quadratic points indeed lie on the curve.
Km23<rtm23>:=QuadraticField(-23);
Km3<rtm3>:=QuadraticField(-3);
Km2<rtm2>:=QuadraticField(-2);
K13<rt13>:=QuadraticField(13);
P1:=X(Km23)![ 1/32*(-11*rtm23 + 47), 1/16*(-7*rtm23 + 43), 1/8*(rtm23 - 5), 1/4*(-rtm23 + 9), 1 ];
P2:=X(Km23)![ 1/2*(rtm23 - 3), 1/2*(rtm23 + 3), 1, 1, 0 ];
P3:=X(Km23)![ 1/2*(-rtm23 + 3), -rtm23 + 2, -1, 1/2*(-rtm23 + 1), 1 ];
P4:=X(Km23)![ 1/8*(rtm23 - 1), 1/8*(rtm23 + 11), 1/4*(-rtm23 - 1), 1/8*(rtm23 + 15), 1 ];
tf,isom:=IsIsomorphic(Parent(j(P2)),Km23);
PP23:=[P1,P2,P3,P4];
P5:=X(Km3)![ 2, 1/2*(-rtm3 + 7), 0, 1/2*(-rtm3 + 5), 1 ];
P6:=X(Km3)![ -rtm3, -rtm3 + 3, 1/2*(rtm3 - 1), -rtm3 + 2, 1 ];
P7:=X(Km3)![ 1/2*(-rtm3 + 3), 1/2*(-rtm3 + 3), 1/2*(rtm3 - 1), 2, 1 ];
P8:=X(Km3)![ 1/2*(-5*rtm3 + 1), 1/2*(-5*rtm3+ 1), 1/2*(rtm3 - 3), -rtm3 + 1, 1 ];
PP3:=[P5,P6,P7,P8];
P9:=X(Km2)![ 1/3*(rtm2 + 4), 1/3*(4*rtm2 + 7), 1/3*(-rtm2 - 1), 1/3*(2*rtm2 + 5), 1 ];
P10:=X(Km2)![ 1/2*(-rtm2+ 2), 3, 1/2*rtm2, 1/2*(-rtm2 + 6), 1 ];
PP2:=[P9,P10];
P11:=X(K13)![ 1/3*(2*rt13 + 14), 1/3*(2*rt13 + 14), 1/6*(-rt13 - 1), 1/6*(5*rt13 + 29), 1 ];
P12:=X(K13)![ 1/2*(5*rt13 + 23), 1/2*(-3*rt13 - 3), 1/2*(rt13 + 3), 1/2*(-rt13 + 3), 1 ];  //No errors means they lie on the curve.
PP13:=[P11,P12];
pls2:=[Place(P1),Place(P2),Place(P3),Place(P4),Place(P5),Place(P6),Place(P7),Place(P8),Place(P9),Place(P10),Place(P11),Place(P12)];

/*We check which ones have CM or are a Q-curve
E23:=[EllipticCurveFromjInvariant(j(P1)),EllipticCurveFromjInvariant(isom(j(P2))),EllipticCurveFromjInvariant(j(P3)),EllipticCurveFromjInvariant(j(P4))];
E3:=[EllipticCurveFromjInvariant(j(Q)) : Q in PP3];
E2:=[EllipticCurveFromjInvariant(j(Q)) : Q in PP2];
E13:=[EllipticCurveFromjInvariant(j(Q)) :Q in PP13];
assert &and[not HasComplexMultiplication(E23[i]) : i in [1..4]];
CMs:=[-27,-3,-12,-3];
for i in [1..4] do
    tf,cm:=HasComplexMultiplication(E3[i]);
    assert cm eq CMs[i];
end for;
tf1,cm1:=HasComplexMultiplication(E2[1]);
assert cm1 eq -8;
tf2,cm2:=HasComplexMultiplication(E2[2]);
assert cm2 eq -8;
assert &and[not HasComplexMultiplication(E13[i]) : i in [1,2]];
c23:=hom<Km23->Km23 | [-rtm23]>;
E23c:=[EllipticCurve([c23(a) : a in aInvariants(EE)]) : EE in E23];
assert &and[not Conductor(E23[i]) eq Conductor(E23c[i]) : i in [1..4]]; //These are not Q-curves
c3:=hom<Km3->Km3 | [-rtm3]>;
PP3c:=[X(Km3)![c3(a) : a in Eltseq(Q)] : Q in PP3];
assert &and[w19(PP3[i]) eq PP3c[i] : i in [1..4]]; //P5,...,P8 are \Q-curves via w_{19}.
assert &and[w57(PP3[i]) eq PP3c[i] : i in [3,4]];
c2:=hom<Km2 -> Km2 | [-rtm2]>;
PP2c:=[X(Km2)![c2(a) : a in Eltseq(Q)] : Q in PP2];
assert &and[w57(PP2[i]) eq PP2c[i] : i in [1,2]];
c13:=hom<K13 -> K13 | [-rt13]>;
PP13c:=[X(K13)![c13(a) : a in Eltseq(Q)] : Q in PP13];
assert &and[w3(PP13[i]) eq PP13c[i] : i in [1,2]];
*/

// We compute all the divisors of degree 2 on X that we found.
pls1:=[Place(c):c in cusps];
deg2:=[1*pl : pl in pls2] cat [1*Place(pt1) + 1*Place(pt2) : pt1 in cusps, pt2 in cusps];
deg2pb:=[];
deg2npb:=deg2; //Just to synchronise with other X_0(N) and make sure the sieve gives no errors.


// cubic points
RR<[x]>:=CoordinateRing(AmbientSpace(X));

I31:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 + 109/54*x[3]*x[5] - 2/27*x[4]*x[5] + 26/27*x[5]^2,
    x[3]*x[4] - 125/54*x[3]*x[5] + 34/27*x[4]*x[5] - 118/27*x[5]^2,
    x[3]*x[5] - 54/1061*x[4]^2 + 130/1061*x[4]*x[5] + 794/1061*x[5]^2,
    x[1] + 7/3*x[3] - 4/3*x[4] + 10/3*x[5],
    x[2] - 5/3*x[3] - 1/3*x[4] - 11/3*x[5]
]>;

I32:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[1]^2 - 11/2*x[1]*x[5] + 3*x[4]*x[5],
    x[1]*x[4] - 3/2*x[1]*x[5] - 3*x[4]*x[5] + 6*x[5]^2,
    x[1]*x[5] - 2*x[4]^2 + 8*x[4]*x[5] - 10*x[5]^2,
    x[2] - 2*x[4] + 2*x[5],
    x[3] + x[4] - 2*x[5]
]>;

I33:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 - 1/3*x[4]*x[5] + 4/3*x[5]^2,
    x[3]*x[4] - 2*x[3]*x[5] + 2/3*x[4]*x[5] - 5/3*x[5]^2,
    x[3]*x[5] - x[4]^2 + 22/3*x[4]*x[5] - 34/3*x[5]^2,
    x[1] - x[4] + x[5],
    x[2] - x[4]
]>;

I34:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 + 11/36*x[3]*x[5] - 7/72*x[4]*x[5] + 25/72*x[5]^2,
    x[3]*x[4] - 31/12*x[3]*x[5] + 11/24*x[4]*x[5] - 29/24*x[5]^2,
    x[3]*x[5] - 4*x[4]^2 + 55/2*x[4]*x[5] - 89/2*x[5]^2,
    x[1] + 8/9*x[3] - 5/9*x[4] - 4/9*x[5],
    x[2] + 2/3*x[3] - 2/3*x[4] - 4/3*x[5]
]>;

I35:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[2]^2 - 3*x[2]*x[5] - 21/4*x[4]*x[5] + 129/8*x[5]^2,
    x[2]*x[4] + x[2]*x[5] - 15/2*x[4]*x[5] + 33/4*x[5]^2,
    x[2]*x[5] + 1/3*x[4]^2 - 17/6*x[4]*x[5] + 4/3*x[5]^2,
    x[1] - 1/2*x[4] - 5/4*x[5],
    x[3] + 1/2*x[5]
]>;

I36:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[2]^2 - x[2]*x[5] - 4*x[4]*x[5] + 2*x[5]^2,
    x[2]*x[4] - 3*x[2]*x[5] + 2*x[4]*x[5] - 10*x[5]^2,
    x[2]*x[5] - x[4]^2 + 5*x[4]*x[5] - 9*x[5]^2,
    x[1] + 2*x[4] - 10*x[5],
    x[3] - x[4] + 4*x[5]
]>;

I37:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[2]^2 - x[2]*x[5] - 4*x[4]*x[5] + 5*x[5]^2,
    x[2]*x[4] - x[4]*x[5] - x[5]^2,
    x[2]*x[5] - 4*x[4]^2 + 5*x[4]*x[5],
    x[1] - x[4] - x[5],
    x[3] - x[4] + x[5]
]>;

I38:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[1]^2 - 3*x[1]*x[5] + 2*x[4]*x[5] - 2*x[5]^2,
    x[1]*x[4] - 2*x[1]*x[5] - x[4]*x[5] + 3*x[5]^2,
    x[1]*x[5] - 2*x[4]^2 + 8*x[4]*x[5] - 10*x[5]^2,
    x[2] - x[4],
    x[3] + x[4] - 2*x[5]
]>;

I39:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 + 1/2*x[3]*x[5] - 1/4*x[4]*x[5] + x[5]^2,
    x[3]*x[4] - 3/2*x[3]*x[5] + 3/4*x[4]*x[5] - 2*x[5]^2,
    x[3]*x[5] - 2/7*x[4]^2 + 25/14*x[4]*x[5] - 16/7*x[5]^2,
    x[1] - x[4] + x[5],
    x[2] + x[3] - x[4]
]>;

I310:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 + 5/3*x[3]*x[5] - 4/3*x[4]*x[5],
    x[3]*x[4] - 1/3*x[3]*x[5] + 8/3*x[4]*x[5] - 4*x[5]^2,
    x[3]*x[5] - 3/7*x[4]^2 + x[4]*x[5] - 9/7*x[5]^2,
    x[1] - 4*x[4] + 2*x[5],
    x[2] + x[3] + x[4] - 3*x[5]
]>;

I311:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[2]^2 - 15/2*x[2]*x[5] + 3*x[4]*x[5] - 3/2*x[5]^2,
    x[2]*x[4] - 2*x[2]*x[5] - 9/2*x[4]*x[5] + 9/2*x[5]^2,
    x[2]*x[5] + 2/3*x[4]^2 - 14/3*x[4]*x[5] + 11/3*x[5]^2,
    x[1] + x[4] - 5*x[5],
    x[3] - x[5]
]>;

I312:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 - 7/31*x[3]*x[5] + 63/124*x[4]*x[5] - 129/124*x[5]^2,
    x[3]*x[4] - 69/31*x[3]*x[5] - 23/31*x[4]*x[5] + 53/31*x[5]^2,
    x[3]*x[5] - 279/32*x[4]^2 + 491/16*x[4]*x[5] - 787/32*x[5]^2,
    x[1] + 5/4*x[4] - 19/4*x[5],
    x[2] - 7/4*x[4] + 5/4*x[5]
]>;

I313:=ideal<CoordinateRing(AmbientSpace(X)) |
[
    x[3]^2 - 7/31*x[3]*x[5] + 63/124*x[4]*x[5] - 129/124*x[5]^2,
    x[3]*x[4] - 69/31*x[3]*x[5] - 23/31*x[4]*x[5] + 53/31*x[5]^2,
    x[3]*x[5] - 279/32*x[4]^2 + 491/16*x[4]*x[5] - 787/32*x[5]^2,
    x[1] + 5/4*x[4] - 19/4*x[5],
    x[2] - 7/4*x[4] + 5/4*x[5]
]>;



II := [I31,I32,I33,I34,I35,I36,I37,I38,I39,I310,I311,I312,I313];

/*
// Assert none of the above cubic points are CM points
for I in II do
E := EllipticCurveFromjInvariant(j(RepresentativePoint(Place(X,I))));
Assert not HasComplexMultiplication(E);
end for;
*/

// Degree 3 pts
deg3npb:=[3*Place(c) : c in cusps] cat [1*Place(c) + DD : c in cusps, DD in deg2npb] cat [Divisor(X,I): I in II];
deg3pb:=[];


//Finally, we do the sieve.
rationalpts :=pls1;
A:=AbelianGroup([0,6,30]);
divs:=[D1,Dtors[1],Dtors[2]];
genusC:=Genus(C);
bp:=3*Place(cusps[1]);
bp1 := Place(cusps[1]); // MWSieve seems to require this, though it's not passed?
bp2 := 2* bp1; // likewise
auts:=[al[1],al[2]];
I:=2;
load "cubicsieve.m";

primes:= [];
smallprimes:=[17,43,47,67,79,181];
assert &and[not IsSingular(ChangeRing(X,GF(p))) : p in smallprimes]; //Sanity check to verify that X has good reduction.
//MWSieve(deg3pb,deg3npb,smallprimes,X,A,divs,auts,genusC,I,bp);
