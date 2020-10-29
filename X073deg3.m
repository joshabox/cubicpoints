//X_0(73). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(73,1); //Takes a while.
X;
assert Genus(X) eq 5;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
M:=al[1];
row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
w:=iso<X->X | row,row>; //The A-L involution w_{73}.

infcusp:=X![1,0,0,0,0]; 
assert 1/j(infcusp) eq 0; 
cusp2:=X![1,1,1,0,0];//
assert 1/j(cusp2) eq 0; //Indeed both are cusps.
assert cusp2 eq w(infcusp); //w acts on the cusps
Dtor:=Divisor(cusp2)-Divisor(infcusp);
assert not IsPrincipal(Dtor); //Sanity check
assert &and[IsPrincipal(6*Dtor), not IsPrincipal(2*Dtor), not IsPrincipal(3*Dtor)]; //So J_0(73)(\Q)_{tor} \simeq Z/6Z.

//We now compute C and J(C)(\Q)
Cprime,projCprime:=CurveQuotient(AutomorphismGroup(X,[w]));
C,h:=SimplifiedModel(Cprime);
XtoC:=Expand(projCprime*h);
C;
assert Genus(C) eq 2;
ptsC:=Setseq(Points(C : Bound:=1000));
J:=Jacobian(C);
assert #TorsionSubgroup(J) eq 1; //J has no torsion.
ptsJ:=[pt-ptsC[2] : pt in ptsC];
Q1:=ptsJ[5];
Q2:=ptsJ[6];
bas,M:=ReducedBasis([Q1,Q2]);
assert #bas eq 2;//This shows J(C)(\Q) has rank 2;
//We will show that Q1,Q2 are a basis using Stoll's algorithm
N:=Orthogonalize(M);
absbd:=Ceiling(Exp((N[1,1]^2+N[1,2]^2+N[2,1]^2+N[2,2]^2)/4+HeightConstant(J)));
//J(C)(\Q) is generated by P1,P2 and all points of height up to absbd.
PtsUpToAbsBound:=Points(J : Bound:=absbd);
assert ReducedBasis([pt : pt in PtsUpToAbsBound]) eq [-Q1,-Q2]; //This shows Q1,Q2 are a basis.


//We use these generators to find the generators of J_0(73)(\Q) modulo torsion
D1:=Pullback(XtoC,Place(ptsC[5])-Place(ptsC[2]));
D2:=Pullback(XtoC,Place(ptsC[6])-Place(ptsC[2]));
Km2<rtm2>:=QuadraticField(-2);
Km19<rtm19>:=QuadraticField(-19);
P3:=X(Km19)![ 1/7*(rtm19 - 10), 1/14*(rtm19 - 17), 1/14*(rtm19 - 17), 1/14*(rtm19 + 11), 1 ];
P6:=X(Km2)![ 1/6*(-rtm2 - 8), -1, 1/6*(-rtm2 - 8), 1/6*(-rtm2 + 4), 1 ];
bp:=Pullback(XtoC,Place(ptsC[2]));
assert bp eq Place(infcusp)+Place(cusp2); 
assert Place(P3) - bp eq D2;
assert Place(P6) - bp eq D1; //So D1 and D2 are indeed as claimed.

//We now verify our list of degree 2 points found using the searchDiv2 function of Siksek and Ozman.
//No error means the points indeed lie on X.
Km31<rtm31>:=QuadraticField(-31);
Km1<rtm1>:=QuadraticField(-1);
Km127<rtm127>:=QuadraticField(-127);
Km3<rtm3>:=QuadraticField(-3);
Km67<rtm67>:=QuadraticField(-67);
P1:=X(Km31)![ 1/32*(-rtm31 - 33), 1/16*(-rtm31 - 9), 1/32*(-3*rtm31 - 35), 1/32*(rtm31 + 17), 1 ];
P2:=X(Km31)![ 1/32*(-rtm31 - 31), 1/16*(rtm31 - 17), -3/2, 1/2, 1 ]; //P1,P2 are the only two exceptional pts
P4:=X(Km1)![ 1/5*(rtm1 - 7), 1/5*(2*rtm1 - 4), 1/5*(3*rtm1 - 6), 1/5*(rtm1 + 3), 1 ];
P5:=X(Km1)![ 1/13*(2*rtm1 - 16), 1/13*(-8*rtm1 - 14), 1/13*(-2*rtm1 - 23), 1/13*(2*rtm1 + 10), 1 ];
P7:=X(Km127)![ 1/32*(-rtm127 - 47), 1/176*(-5*rtm127 - 163), 1/22*(-rtm127 - 26), 1/44*(-rtm127 + 29), 1 ];
P8:=X(Km3)![ 1/26*(-9*rtm3 - 41), 1/52*(-15*rtm3 - 51), 1/26*(-9*rtm3 - 28), 1/52*(-9*rtm3 + 37), 1 ];
P9:=X(Km3)![ -1, 1/4*(rtm3 - 3), 1/4*(rtm3 - 5), 1/2, 1 ];
P10:=X(Km3)![ -1, 1/2*(rtm3 - 3), -2, 1, 1 ];
P11:=X(Km67)![ 1/23*(-4*rtm67 - 43), 1/46*(-7*rtm67 - 35), 1/23*(-3*rtm67 - 15), 1/23*(-rtm67 + 18), 1 ];
pls2:=[Place(P1),Place(P2),Place(P3),Place(P4),Place(P5),Place(P6),Place(P7),Place(P8),Place(P9),Place(P10),Place(P11)];
assert [Place(P1),Place(P2)] eq [PP : PP in pls2 | not XtoC(RepresentativePoint(PP)) in C(Rationals())]; //Indeed only P1,P2 are exceptional.
assert #ptsC eq 10; //This matches up: we have 9 non-exceptional quadratic pts and 
assert #PointSearch(X,1000) eq 2; //one pair of cusps mapping to 10 rational points on C.
//We compute all the divisors of degree 2 on X that we found.
deg2:=[1*pl : pl in pls2] cat [1*Place(pt1)+1*Place(pt2) : pt1 in [infcusp,cusp2], pt2 in [infcusp,cusp2]];
pls1:=[Place(infcusp),Place(cusp2)];
deg2pb:=[1*pl : pl in pls2 | XtoC(RepresentativePoint(pl)) in C(Rationals())] cat 
[1*pl1 + 1*pl2 : pl1 in pls1, pl2 in pls1 | w(RepresentativePoint(pl1)) eq RepresentativePoint(pl2)];
deg2npb:=[DD : DD in deg2 | not DD in deg2pb]; //We split deg2 into deg2 \cap XtoE*(E(\Q)) and the rest.
assert Seqset(deg2) eq Seqset(deg2pb cat deg2npb); //Sanity check.

cusps:=[infcusp,cusp2];
rationalpts:=[Place(c) : c in cusps];
bp:=2*Place(infcusp)+Place(cusp2);
bp2:=Place(infcusp)+Place(cusp2);
bp1:=Place(infcusp);
V,phi:=RiemannRochSpace(bp+3*D1-D2+2*Dtor);
excpl:=Divisor(phi(V.1))+bp+3*D1-D2+2*Dtor;
V,phi:=RiemannRochSpace(bp+3*D1-D2-Dtor);
excpl2:=Divisor(phi(V.1))+bp+3*D1-D2-Dtor;
deg3pb:=Setseq({<Place(c),DD> : c in cusps,DD in deg2pb});
deg3pbsum:=[DD[1]+DD[2] : DD in deg3pb];
deg3npb:=Setseq({Place(c)+DD : c in cusps, DD in deg2npb | not (Place(c)+DD) in deg3pbsum}) cat [excpl,excpl2];  

R<t> := PolynomialRing(Rationals());
K<a> := NumberField(R![ 8, 7, -1, 1 ]);

for DDD in [excpl,excpl2] do
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
assert not HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;

//Finally, we do the sieve.
primes:=[];
smallprimes:=[19,41,59,43,13,103];
A:=AbelianGroup([0,0,6]);
divs:=[D1,D2,Dtor];
genusC:=Genus(C);
auts:=[al[1]];
I:=1;

load "Cubicsieve.m";

//We check that indeed the matrix for 3*cusp has rank 2 over the rationals.
for Q in cusps do
    tQ:=UniformizingParameter(Place(Q));
    etas:=[ALMap(X,aut) : aut in auts];
    V,phii:=SpaceOfDifferentialsFirstKind(X);
    ts:=[hom<V->V | [ (Pullback(eta,phii(V.i)))@@phii -V.i  : i in [1..Genus(X)] ]> : eta in etas];
    T:=&+[Image(t) : t in ts]; //The space of ann. diffs. of trace zero.
    omegas:=[phii(T.i) : i in [1..Dimension(T)]]; //A list of lin. indep. ann. diffs. of trace zero.
    M:=Matrix([ExpandDifferential(om,Q,tQ,2) : om in omegas]);
    assert Ncols(M) eq 3 and Nrows(M) eq 3;
    assert Rank(M) eq 2;
 end for;
 
 badpts:=[];
 for Q in deg3npb do
    if not Q in [3*Place(cusps[1]),3*Place(cusps[2])] then
        Append(~badpts,false);
        else Append(~badpts,true);
    end if;
 end for;

/*for p in primes do
    p;
    Fp:=GF(p); Fp2:=GF(p^2);
    Xp:=ChangeRing(X,Fp);
    CC,phi,psi:=ClassGroup(Xp);
    Z:=FreeAbelianGroup(1);
    degr:=hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
    JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
    Factorization(#JFp);
end for;*/



MWSieve(deg3pb,deg3npb,badpts,smallprimes,X,A,divs,auts,genusC,I,bp);

