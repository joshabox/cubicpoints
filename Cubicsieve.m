//The following function computes the expansion of a differential 
//om around the uniformizer tQ of a point Q, up to the (n+1)th coefficient a_n.
ExpandDifferential:=function(om,Q,tQ,n)
assert n ge 0;
dt:=Differential(tQ);
f:=om/dt;
FF:=Parent(f);
K:=Parent(Eltseq(Q)[1]);
XK:=ChangeRing(X,K);
Qpt:=XK!Eltseq(Q);
CRK<[xK]>:=CoordinateRing(AmbientSpace(XK));
FK:=FunctionField(XK);
f:=FK!(Evaluate(Numerator(ProjectiveFunction(f)),xK)/Evaluate(Denominator(ProjectiveFunction(f)),xK));
tQ:=FK!(Evaluate(Numerator(ProjectiveFunction(tQ)),xK)/Evaluate(Denominator(ProjectiveFunction(tQ)),xK));
alist:=[Evaluate(f,Qpt)];
if n gt 0 then
flist:=[(f-(Evaluate(f,Qpt)))/tQ];
for i in [1..n] do
    Append(~alist,flist[i](Qpt));
    Append(~flist,(flist[i]-alist[i+1])/tQ);
end for;
end if;
return alist;
end function;

IsLonely:=function(QQ,X,Xp,p,auts,genusC,omegas)
if p le 13 then return false; end if; //Part of first condition in Theorem
d:=3; //Just there to emphasize that we work on X^{(d)} for d=3.
Fp:=BaseRing(Xp);
Rp<[u]>:=CoordinateRing(AmbientSpace(Xp));
n:=Dimension(AmbientSpace(X)); //Assuming X is given in projective space
matrixseq:=[];
dec:=Decomposition(reduce(X,Xp,QQ));
Fq:=GF(p^(LCM([Degree(ResidueClassField(dd[1])) : dd in dec])));
//Thm 3.2 of Samir also works with (a0,a1/2) when Q_1 neq Q_2 but Q1tilde = Q2tilde.
for i in [1..#dec] do
    Qtilde:=dec[i][1]; 
    m:=dec[i][2];
    Kp:=ResidueClassField(Qtilde);
    Embed(Kp,Fq);
    Qtildept:=Eltseq(RepresentativePoint(Qtilde));
    if Degree(Kp) eq 1 then frobs:=[IdentityHomomorphism(Kp)];
    else
    frob:=hom< Kp->Kp | (Kp.1)^p >;
    frobs:=[frob];
    for j in [1..Degree(Kp)-1] do
        Append(~frobs,frob*frobs[#frobs]);
    end for;
    end if;
    assert #frobs eq Degree(Kp);
    Qtildes:=[Xp(Kp)![fr(a) : a in Qtildept] : fr in frobs];
    tQtildes:=[UniformizingParameter(Qtilde) : Qtilde in Qtildes];
    for k in [1..#tQtildes] do
        omlist:=[ExpandDifferential(om,Qtildes[k],tQtildes[k],m-1) : om in omegas];
        for jj in [1..m] do
        Append(~matrixseq,[Fq!om[jj]/jj : om in omlist]);
        end for;
    end for;
end for;
Atilde:=Matrix(matrixseq);
if Rank(Atilde) eq d then return true;

elif Rank(Atilde) eq d-1 and m eq d then
    Fqq:=GF(p^3);
    Embed(Fq,Fqq);
    matrixseq:=[];
    omlist:=[ExpandDifferential(om,Qtildes[1],tQtildes[1],m) : om in omegas];
    for jj in [1..m+1] do
        Append(~matrixseq,[Fq!om[jj]/jj : om in omlist]);
    end for;
    Atilde:=Matrix(matrixseq);
    K:=Kernel(Atilde);
    assert Dimension(K) eq 1;
    b:=Eltseq(Basis(K)[1]);
    A4<z1,z2,z3,lambda>:=AffineSpace(Fq,4);
    S:=Scheme(A4,[z1+z2+z3-lambda*b[1],z1^2+z2^2+z3^2-lambda*b[2],z1^3+z2^3+z3^3-lambda*b[3],z1^4+z2^4+z3^4-lambda*b[4]]);
    if #Points(S,Fqq) eq 1 then return true;
    //No points over F_{p^3} and F_p means there can be no degree 3 or 2+1 divisor in the residue class of QQ.
    else return false;
    end if;
else return false;
end if;
end function;


ALMap := function(X,auts)
R<[u]>:=CoordinateRing(AmbientSpace(X));
n:=Dimension(AmbientSpace(X)); //Assuming X is given in projective space
row:=[&+[RowSequence(auts[1])[i][j]*u[j] : j in [1..n+1]] : i in [1..n+1]]; 
//Note that this function is only called upon for N \neq 57 so #auts = 1
return iso<X -> X | row,row>;
end function;
eta:=ALMap(X,auts);

IsOnlyWithFamily:=function(ratpt,pb,X,Xp,p,auts,genusC,omegas)
Fp:=BaseRing(Xp); Fp2:=GF(p^2);
p:=Characteristic(Fp);
Embed(Fp,Fp2);
if p lt 14 then
return false;
end if;

// We first check if pb is a sum of rational pts
rational := false;
AwkwardDivisor := false;
n := #rationalpts;
for i in {x: x in CartesianProduct([{1 .. n},{1..n}])| x[1] le x[2]} do
if pb eq (rationalpts[i[1]]+ rationalpts[i[2]]) then
rational := true;
K := RationalsAsNumberField();
index := [Index(rationalpts, ratpt),i[1],i[2]];
break;
end if;
end for;

if rational then
  if Multiplicity(index,index[1]) eq 3 then
   ImportantPoints := [ratpt]; // need to select "w(Q)" (=Q here)
   AwkwardDivisor := true;
  elif (Multiplicity(index,index[1]) eq 2) then
   ImportantPoints := (Multiplicity(index,index[2]) eq 2) select [rationalpts[index[3]]] else  [rationalpts[index[2]]]; // need to select "w(Q)"
   AwkwardDivisor := true;
   assert Pullback(eta, ratpt) eq ImportantPoints[1]; // check we've selected "w(Q)"
  else
   ImportantPoints := [ratpt, rationalpts[index[2]]]; // all points are distinct, so we take ratpt and one of the points from the pullback
   //assert (index[1]-index[2])*(index[1]-index[3])*(index[2]-index[3]) ne 0; //check
  end if;
  ImportantPoints:=[reduce(X,Xp,IP) : IP in ImportantPoints];
else
 Decomp := Decomposition(1*reduce(X,Xp,pb)); // decompose pullback
 ImportantPoints := [reduce(X,Xp,ratpt),Decomp[1][1]];
end if;

Arows := [];

for Qtilde in ImportantPoints do
assert Type(Qtilde) eq PlcCrvElt;
Kp:=ResidueClassField(Qtilde);
Embed(Kp,Fp2);
tQtilde:=UniformizingParameter(Qtilde);
Append(~Arows,[Fp2!Evaluate(omega/Differential(tQtilde),Qtilde) : omega in omegas]);
if AwkwardDivisor then
Append(~Arows,[Fp2!Evaluate((omega/Differential(tQtilde)-Evaluate(omega/Differential(tQtilde),Qtilde))/tQtilde,Qtilde) : omega in omegas]);
end if;
end for;

Atilde:=Matrix(Arows);
if Rank(Atilde) eq #Arows then return true;
else return false;
end if;
end function;

ChabautyInfo:=function(Lpb,Lnpb,p,X,auts,genusC,A,B,iA,W,divs,I,bp)
Fp:=GF(p); Fp2:=GF(p^2);
Xp:=ChangeRing(X,Fp);
Rp<xp,yp,zp>:=CoordinateRing(AmbientSpace(Xp));
Cp:=ChangeRing(C,Fp);
CC,phi,psi:=ClassGroup(Xp);
Z:=FreeAbelianGroup(1);
degr:=hom<CC->Z | [ Degree(phi(a))*Z.1 : a in OrderedGenerators(CC)]>;
JFp:=Kernel(degr); // This is isomorphic to J_X(\F_p).
divsp:=[reduce(X,Xp,divi) : divi in divs];
bpp:=reduce(X,Xp,bp); //We reduce the divisors and the basepoint
bpp1:=reduce(X,Xp,bp1);
bpp2:=reduce(X,Xp,bp2);
h:=hom<A -> JFp | [JFp!psi(divp) : divp in divsp]>; //The map A --> J_X(\F_p).

Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
WW:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
mI:=hom<JFp -> JFp | [I*g : g in OrderedGenerators(JFp)]>;
imW:={h(x) : x in WW | h(x) in Image(mI)}; //The possible images in JFp of unknown rat. pts., (before mult. by n.)
K:=Kernel(mI);

//JFp often contains factors Z/qZ with q a large prime. If there is no (or few) other prime p' such that JFp' also contains a Z/qZ factor, then this mod q information is (almost) useless. This is likely to happen for large q. Hence we choose only to consider the mod q information for q le 23. This speeds up computations, as the index of B in A remains small.
fact:=Factorisation(#JFp);
n:=&*([1] cat [pp[1]^(pp[2]) : pp in fact | pp[1] gt 23]);
mn:=hom<JFp -> JFp | [n*g : g in OrderedGenerators(JFp)]>; 

// Compute ann. differentials of trace zero
etap:=ALMap(Xp,auts);
V,phii:=SpaceOfDifferentialsFirstKind(Xp);
t:=hom<V->V | [ (Pullback(etap,phii(V.i)))@@phii -V.i  : i in [1..Genus(X)] ]>;
T:=Image(t); //The space of ann. diffs. of trace zero.
if not p eq 2 then assert Dimension(T) eq Genus(X) - genusC; end if;
omegas:=[phii(T.i) : i in [1..Dimension(T)]]; //A list of lin. indep. ann. diffs. of trace zero.

redL1pb:=[<reduce(X,Xp,DD[1]),reduce(X,Xp,DD[2])> : DD in Lpb];
redL1npb:=[reduce(X,Xp,DD) : DD in Lnpb];
redLpb:=[<JFp!psi(DD[1]-bpp1),JFp!psi(DD[2]-bpp2)> : DD in redL1pb]; 
redLpbsum:=[DD[1]+DD[2] : DD in redLpb];
redLnpb:=[JFp!psi(DD-bpp) : DD in redL1npb];
mnjposP:=[];

for x in imW do
    if not mn(x) in mnjposP then //This if statement is usually not satisfied,thus saving us from a lot of unnecessary work.
    z:=x@@mI; //We reconstruct possible mod p points from their image in JFp, by first taking inverse images under mI.
    if &or[Dimension(phi(z+k)+bpp) gt 0 and ( (p in [3,7,11,13]) or (not (z+k) in redLnpb cat redLpbsum) or ((z+k) in redLnpb and not IsLonely(Lnpb[Index(redLnpb,z+k)],X,Xp,p,auts,genusC,omegas)) or ((z+k) in redLpbsum and not IsOnlyWithFamily(Lpb[Index(redLpbsum,z+k)][1],Lpb[Index(redLpbsum,z+k)][2],X,Xp,p,auts,genusC,omegas)) ) : k in K] then
        Append(~mnjposP,mn(x)); //Finally we only store the information multiplied by n.
    end if;
    end if;
end for;

print "The nr of pts in mnjposP is"; #mnjposP;
h:=h*mn;
Bp,iAp:=sub<A | Kernel(h)>;
newB,newiA:=sub<A | iA(B) meet iAp(Bp)>;
AmodnewB,pi1:=quo< A | newiA(newB)>;
AmodB,pi2:=quo<AmodnewB | pi1(iA(B))>;
W:=[(x+w)@@pi1 : x in Kernel(pi2), w in pi1(W)];
B:=newB; iA:=newiA;
W:=[x : x in W | h(x) in mnjposP];
return W,B,iA; 
end function;

MWSieve:=function(Lpb,Lnpb,smallprimes,X,A,divs,auts,genusC,I,bp)
print "Welcome to our sieve.";
print "If I return true then all points are known.";

// We now set up the sieve.
B,iA:=sub<A|A>; // This subgroup will shrink as we consider more primes. 
W:={0*A.1}; // This will be our set of possible B-cosets in A. Will grow.
// Together, B+W \subset A consists of the possible images of unknown (rational)
// points in A. The map X(\Q) \to A is composition of X(\Q) \to J(X)(\Q) and
// multiplication by integer I such that I*J(X)(\Q) \subset A.
for p in smallprimes do
print "We consider the prime"; p;
W,B,iA:=ChabautyInfo(Lpb,Lnpb,p,X,auts,genusC,A,B,iA,W,divs,I,bp);
print "The number of cosets in J(X)(Q) where unknown points can land is"; #W;
smallsols:=[w : w in W | &+[AbsoluteValue(Integers()!a) : a in Eltseq(w)] lt 100];
if #smallsols gt 0 then smallsols; end if;
if W eq [] then 
print "Wait, did I say 0? I guess I did, didn't I? That must mean that there aren't any unknown points then, hurray!";
return true; end if;
end for;

return W,B,iA;
end function;
