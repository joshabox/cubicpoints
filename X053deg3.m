//X_0(53). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(53,1); //Takes a minute or 2.
X;
assert Genus(X) eq 4;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
M:=al[1];
row:=[&+[RowSequence(M)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]];
w:=iso<X->X | row,row>; //The A-L involution w_{53}.

infcusp:=X![1,0,0,0]; 
assert 1/j(infcusp) eq 0; 
cusp2:=X![1,1,1,1];//
assert 1/j(cusp2) eq 0; //Indeed both are cusps.
assert cusp2 eq w(infcusp); //w acts on the cusps
cusps:=[infcusp,cusp2];
Dtor:=Divisor(cusp2)-Divisor(infcusp);
assert not IsPrincipal(Dtor); //Sanity check
assert IsPrincipal(13*Dtor); //So J_0(43)(\Q)_{tor} \simeq Z/13Z.

//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w]));
Eprime,hprime:=EllipticCurve(C,projC(infcusp));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 53;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([0])); //Shows MWE is free of rank 1
seqQE:=[QQ : QQ in [phi(MWE.1),phi(-MWE.1)] | QQ eq E![0,-1,1]];
QE:=seqQE[1]; //QE is the claimed point. 

//We use this generator to find the free generator of G \subset J_0(53)(\Q)
D:=Pullback(XtoE,Place(QE));
D1:=D-1*Place(infcusp)-1*Place(cusp2);
K11<r>:=QuadraticField(-11);
assert r^2 eq -11;
PP:=(X(K11)![ 0, 1/6*(-r + 5), 1, 1 ]);
assert Place(PP) eq D; //This shows the generator is as claimed.
bp2:=Pullback(XtoE,Place(E![0,1,0]));
assert bp2 eq Place(infcusp)+Place(cusp2); //Sanity check.
bp1:=Place(cusps[1]);
bp:=bp2+bp1;
deg2pb:=[Pullback(XtoE,Place(n*QE)) : n in [-12..12]];
deg3pb:=[<Place(pt),DD> : pt in cusps,DD in deg2pb];
//The following two ideals corresponding to degree 3 places were found using searchDiv2
RR<[x]>:=CoordinateRing(AmbientSpace(X));
I1:=ideal<CoordinateRing(AmbientSpace(X)) | [
    x[2]^2 - 343/178*x[2]*x[4] - 325/178*x[3]*x[4] + 212/89*x[4]^2,
    x[2]*x[3] - 109/178*x[2]*x[4] + 72/89*x[3]*x[4] - 66/89*x[4]^2,
    x[2]*x[4] - 89/12*x[3]^2 + 557/24*x[3]*x[4] - 85/6*x[4]^2,
    x[1] - x[2] - 3*x[3] + 3*x[4]
]>;
I2:=ideal<CoordinateRing(AmbientSpace(X)) | [
    x[1]^2 - 10/9*x[1]*x[3] + 5/3*x[2]*x[3] - 10/9*x[3]^2,
    x[1]*x[2] + 2/3*x[1]*x[3] + 5/3*x[3]^2,
    x[1]*x[3] - x[2]^2 - 2/3*x[3]^2,
    x[4]
]>;
//And the following eight degree 3 places were found by running the sieve and finding "small vectors" in J(X)(\Q) that remained.
extraplscoeffs:=[[3,4],[-1,-5],[2,6],[-2,-3],[-2,4],[2,-5],[-1,6],[3,-3]];
extraDs:=[];
for nn in extraplscoeffs do
    a:=nn[1];
    b:=nn[2];
    V,phi:=RiemannRochSpace(bp+a*D1+b*Dtor);
    assert Dimension(V) eq 1;
    f:=phi(V.1);
    Append(~extraDs,bp+a*D1+b*Dtor+Divisor(f));
end for;
deg3npb:=[3*Place(cusps[1]),3*Place(cusps[2])] cat [Divisor(X,I1),Divisor(X,I2)] cat extraDs;

assert not IsSingular(ChangeRing(X,GF(17))) and not IsSingular(ChangeRing(X,GF(31)));


R<t> := PolynomialRing(Rationals());
K<a> := NumberField(R![52, 5, -1, 1]); ///cubic field with discriminant = -3.5.5197

// We now express all representatives of all degree 3 points.
for DDD in [Divisor(X,I1),Divisor(X,I2)] do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));// As Q(root(-83)) has class number 3 with Hilbert class field K(root(-83)), I'm quite surprised this comes back false.
end for;

K<a> := NumberField(R![-8, 11, 0, 1]); ///cubic field with discriminant -1763 = -41.43

for DDD in [extraDs[1],extraDs[8]] do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));// As Q(root(-83)) has class number 3 with Hilbert class field K(root(-83)), I'm quite surprised this comes back false.
end for;

K<a> := NumberField(R![147, 53, -1, 1]); // cubic field of discriminant -328948

for DDD in [extraDs[2],extraDs[7]] do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;

K<a> := NumberField(R![-3, -2, 0, 1]); // cubic field of discriminant -211

for DDD in [extraDs[3],extraDs[6]] do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;

K<a> := NumberField(R![-4, -3, 0, 1]); // cubic field of discriminant -324

for DDD in [extraDs[4],extraDs[5]] do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;



//Finally, we do the sieve.
rationalpts:=[Place(c) : c in cusps];
A:=AbelianGroup([0,13]);
divs:=[D1,Dtor];
genusC:=Genus(C);
auts:=[al[1]];
I:=2;
badpts:=[false : i in deg3npb];

load "Cubicsieve.m";
primes:=[];
smallprimes:=[31,17];
MWSieve(deg3pb,deg3npb,badpts,smallprimes,X,A,divs,auts,genusC,I,bp);

