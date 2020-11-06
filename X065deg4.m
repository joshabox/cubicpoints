//X_0(65). Load searchDiv2, reduce, modeqns
load "ozmansiksek.m";

X,Z,phi,j,al,jd:=modeqns(65,13); //Just a few seconds.
X;
assert Genus(X) eq 5;

RR<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X));
rows:=[[&+[RowSequence(a)[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]] : a in al] ;
w5:=iso<X->X | rows[1],rows[1]>; 
w13:=iso<X->X | rows[2], rows[2]>; 
w65:=iso<X->X | rows[3] , rows[3]>; //These are the Atkin-Lehner involutions.
assert w65 eq w5*w13; //Sanity check

load "X065quarticpts.m";

cusps:=[X![1,0,0,0,0],X![1,1,1,1,1],X![1/3,2/3,2/3,2/3,1],X![1/2,1/2,1/2,1/2,1]]; 
assert &and[1/j(cusp) eq 0 : cusp in cusps]; //We have found the four cusps.
assert {w(cusps[1]) : w in [w5*w5,w5,w13,w65]} eq Seqset(cusps);
Dtors:=[Divisor(cusps[i])-Divisor(cusps[1]) : i in [2,3,4]];
assert &and[not IsPrincipal(Dtor) : Dtor in Dtors]; //Sanity check
//To compute the rational cuspidal subgroup, we embed the torsion subgroup into J_X(\F_7)
X7:=ChangeRing(X,GF(7));
C,phi,psi:=ClassGroup(X7);
Z:=FreeAbelianGroup(1);
degr:=hom<C->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(C)]>;
JF7:=Kernel(degr); // This is isomorphic to J_X(\F_7).
redDtors:=[JF7!psi(reduce(X,X7,DD)) : DD in Dtors];
A:=sub<JF7 | redDtors>; //This is isomorphic to J_X(\Q)_{tors}.
B:=AbelianGroup([2,84]);
tf,isomm:=IsIsomorphic(A,B);
assert tf; 
assert &and[isomm(A.i) eq B.i : i in [1,2]]; //So A = Z/2Z x Z/84Z with A.1, A.2 being the generators
Z3:=FreeAbelianGroup(3);
hh:=hom<Z3-> A | redDtors>;
assert hh(-9*Z3.1+2*Z3.2) eq A.1;
assert Order(hh(17*Z3.1+13*Z3.2)) eq 84 and not 42*hh(17*Z3.1+13*Z3.2) eq hh(-9*Z3.1+2*Z3.2); //This shows that the generators of J_X(\Q)_{tors} are as claimed.


//We now compute C and J(C)(\Q)
C,projC:=CurveQuotient(AutomorphismGroup(X,[w65]));
Eprime,hprime:=EllipticCurve(C,projC(cusps[1]));
E,h:=SimplifiedModel(Eprime);
XtoE:=Expand(projC*hprime*h);
E;
assert Conductor(E) eq 65;
MWE,phi,tf1,tf2:=MordellWeilGroup(E);
assert tf1; assert tf2; //This shows MWE is computed provably.
assert IsIsomorphic(MWE,AbelianGroup([2,0])); //Shows MWE is Z/2Z x Z as abstract group.
assert 2*MWE.1 eq Zero(MWE); //So MWE.1 is the generator of order 2.
DD:=Pullback(XtoE,Place(phi(MWE.1)));
assert DD eq Place(cusps[3])+Place(cusps[4]); //The pullback of the divisor phi(MWE.1)-Zero(E) to X is already torsion.
seqQE:=[QQ : QQ in [phi(MWE.2),phi(-MWE.2)] | QQ eq E![1,0,1]];
QE:=seqQE[1]; //QE is the claimed point.



//We use this generator to find the free generator of J_0(43)(\Q)
D:=Pullback(XtoE,Place(QE));
bp:=Pullback(XtoE,Place(Zero(E)));
bp4 := 2*bp;
assert bp eq Place(cusps[1]) + Pullback(w65,Place(cusps[1])); //Sanity check
D1:=D-bp;
K1<r>:=QuadraticField(-1);
assert r^2 eq -1;
PP:=(X(K1)![0,1,1/2*(1+r),1,1]);
assert 1*Place(PP) eq D; //This shows the generator is as claimed.


//We compute quadratic points on X via rational points on E. 
ptsX:=PointSearch(X,1000);
deg2pb:=[Pullback(XtoE,Place(phi(k*MWE.2+ep*MWE.1))) : k in [-17..17], ep in [0,1]] cat [Pullback(XtoE,Place(pt)) : pt in PointSearch(E,1000)];
deg1p1:=Setseq({Place(pt1) + Place(pt2) : pt1 in ptsX, pt2 in ptsX});
deg2npb:=[Place(pt1) + Place(pt2) : pt1 in ptsX, pt2 in ptsX | not w65(pt1) eq pt2];
deg2pb:=[DD : DD in deg1p1 | not DD in deg2npb] cat deg2pb; //We split into pullbacks and non-pullbacks.
deg3pb:=[<Place(pt1),DD> : pt1 in ptsX, DD in deg2pb];
//deg3npb:=[Divisor(pt1)+Divisor(pt2)+Divisor(pt3) : pt1 in ptsX, pt2 in ptsX, pt3 in ptsX | #({pt1,pt2,pt3} meet {w65(pt1),w65(pt2),w65(pt3)}) eq 0];
deg4npb:=[Divisor(pt1)+Divisor(pt2)+Divisor(pt3) +Divisor(pt4): pt1 in ptsX, pt2 in ptsX, pt3 in ptsX, pt4 in ptsX | #({pt1,pt2,pt3,pt4} meet {w65(pt1),w65(pt2),w65(pt3),w65(pt4)}) eq 0];
deg4pbQuad := [<DD1,DD2,2> : DD1 in deg2pb, DD2 in deg2pb] cat [<DD1,DD2,3> : DD1 in deg2npb, DD2 in deg2pb];
//deg4pbsum :=  [DD1+DD2 : DD1 in deg2pb, DD2 in deg2pb] cat [DD1+DD2 : DD1 in deg2npb, DD2 in deg2pb];

// We now compute quartic points on X via quadratic points on E.
Edeg2 := searchDiv2(E,5,false); // I can increase the bound if need be
deg4pbQuart :=[];
for D in Edeg2 do
dec := Decomposition(D);
deg := Degree(dec[1][1]);
if deg eq 1 and #dec eq 2 then
Append(~deg4pbQuad,<Pullback(XtoE,dec[1][1]),Pullback(XtoE,dec[2][1]),2>);
continue; 
end if;
Pb := Pullback(XtoE,dec[1][1]);
dec := Decomposition(Pb);
Pl := dec[1][1];
if Degree(Pl) eq 4 then
Append(~deg4pbQuart,1*Pl);
//else
//assert #dec eq 2;
end if;
end for;





RR<[x]>:=CoordinateRing(AmbientSpace(X));

//After a long search using the searchDiv2 function (written by Ozman and Siksek) above, we found four extra (exceptional) Galois orbits of cubic points.
I31:=ideal<CoordinateRing(AmbientSpace(X)) | [
    x[3]^2 - 4/3*x[3]*x[5] - 41/129*x[4]*x[5] + 74/129*x[5]^2,
    x[3]*x[4] - 1/3*x[3]*x[5] - 119/129*x[4]*x[5] + 26/129*x[5]^2,
    x[3]*x[5] - 3*x[4]^2 + 122/43*x[4]*x[5] - 44/43*x[5]^2,
    x[1] + x[3] - x[4] - x[5],
    x[2] - 2/3*x[3] - 1/3*x[4] + 1/3*x[5]
]>;
I32:=ideal<CoordinateRing(AmbientSpace(X)) | [
    x[3]^2 - 15/2*x[3]*x[5] - x[4]*x[5] + 6*x[5]^2,
    x[3]*x[4] + x[3]*x[5] - 1/2*x[4]*x[5] - x[5]^2,
    x[3]*x[5] - 2*x[4]^2 + 3*x[4]*x[5] - 2*x[5]^2,
    x[1] - 10*x[3] - 2*x[4] + 9*x[5],
    x[2] + 3*x[3] - 3*x[5]
]>;
I33:=ideal<CoordinateRing(AmbientSpace(X)) | [
    x[3]^2 - 25/32*x[3]*x[5] + 23/32*x[4]*x[5] - 13/32*x[5]^2,
    x[3]*x[4] - 13/16*x[3]*x[5] + 3/16*x[4]*x[5] - 1/16*x[5]^2,
    x[3]*x[5] - 8*x[4]^2 + 9*x[4]*x[5] - 3*x[5]^2,
    x[1] + 8*x[4] - 6*x[5],
    x[2] - 2*x[3] + 5*x[4] - 3*x[5]
]>;
I34:=ideal<CoordinateRing(AmbientSpace(X)) | [ x[3]^2 - 135/92*x[3]*x[5] + 1/4*x[4]*x[5] + 59/184*x[5]^2,
    x[3]*x[4] - 39/46*x[3]*x[5] - 1/2*x[4]*x[5] + 19/46*x[5]^2,
    x[3]*x[5] + 23*x[4]^2 - 69/2*x[4]*x[5] + 47/4*x[5]^2,
    x[1] - 4*x[3] + 4*x[4] - x[5],
    x[2] - 4*x[3] + 3*x[4] - 1/2*x[5]
]>;
Is:=[I31,I32,I33,I34];
excDs:=[Divisor(X,II) : II in Is];
assert &and[Degree(DD) eq 3 : DD in excDs];
//deg3npb:=deg3npb cat excDs;


R<t> := PolynomialRing(Rationals());
K<a> := NumberField(R![-2, 1, -1, 1]); ///cubic field with discriminant = -83

// We now express all representatives of all degree 3 points.
for DDD in excDs do
"Next point";
Pt := RepresentativePoint(Decomposition(DDD)[1][1]);
F := Parent(Pt[1]);
tf, phi := IsIsomorphic(F,K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
EPt := EllipticCurveFromjInvariant(j(Pt));
assert not HasComplexMultiplication(EPt);
L := NormalClosure(F);
GaloisConjugates :=[X(L)![sigma(coef): coef in Eltseq(Pt)]: sigma in Automorphisms(L)];
assert not &and[Conductor(EPt) eq Conductor(EllipticCurveFromjInvariant(j(sigmaPt))): sigmaPt in GaloisConjugates];
end for;

NewDivs := [Divisor(X,I): I in deg4npbnew];
Fields := [<[1, 0, 3, 0, 1],400>, <[1, 1, 2, -1, 1],225>,<[10, 4, -4, -2, 1], 2368>,<[36, 0, -5, 0, 1], 14161>,<[ 64, 0, -1, 0, 1 ],65025>,<[ 6, -13, 10, 0, 1 ],567509>,
<[ 324, 124, 33, -2, 1 ],25993253>,<[-4, 2, 2, -2, 1],-2284>,<[8, 3, -6, -2, 1],-36787>,<[4, -12, -5, -1, 1], -75427>,<[8, 15, 1, -1, 1],  -211044>,
<[ -1587, -36, 22, 0, 1 ],-22142892>,<[ -376, -612, -26, -1, 1 ],-77994564>]; // We use pari/gp's redpolabs function 

DivsAndFields :=[];
for DD in NewDivs do
Pt := RepresentativePoint(Decomposition(DD)[1][1]);
F := AbsoluteField(Parent(Pt[1]));
Disc := Discriminant(Integers(F));
Append(~DivsAndFields,<DD,Disc>);
end for;

for entry in Fields do
K := NumberField(R!entry[1]);K;
Pts := [DF[1]: DF in DivsAndFields |DF[2] eq entry[2]];
for DD in Pts do
Pt := RepresentativePoint(Decomposition(DD)[1][1]);
F := AbsoluteField(Parent(Pt[1]));
tf, phi := IsIsomorphic(F, K);
assert tf;
X(K)![phi(coef): coef in Eltseq(Pt)];
phi(j(Pt));
HasComplexMultiplication(EllipticCurveFromjInvariant(j(Pt)));
end for;
end for;


deg4npb := deg4npb cat [Divisor(pt) + D: pt in ptsX, D in excDs] cat [Divisor(X,I) : I in deg4npbnew];
deg4pbQuartic := [Divisor(X,I) : I in deg4pbnew] cat deg4pbQuart;

//Finally, we do the sieve.
assert &and[not IsSingular(ChangeRing(X,GF(p))) : p in [17,23]]; //Sanity check to verify that X has good reduction at primes used in the sieve.
A:=AbelianGroup([0,2,84]);
divs:=[D1,-9*Dtors[1]+2*Dtors[2],17*Dtors[1]+13*Dtors[2]];
genusC:=Genus(C);
auts:=[al[3]];
I:=1;
bp2:=bp; assert Degree(bp2) eq 2;
bp:=2*bp; //Need a basepoint of degree 4
bp1:=Divisor(cusps[1]);
smallprimes := [17,19,23];
load "quarticsieve.m";


MWSieve(deg4pbQuad, deg4pbQuartic,deg4npb,smallprimes,X,A,divs,auts,genusC,I,bp); //Returns true if we have found all deg 4 points.

