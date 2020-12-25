// This code is a partial implementation of the algorithm described in Cremona and Najman's paper "Q-curves over odd degree number fields" https://arxiv.org/abs/2004.10054

// The following function takes a j-invariant and returns:
// 1) true, D -  if the EC has CM by the quadratic order defined by D
// 2) false, and a statement - if the EC has been shown not to be a Q-curve. The statment indicates which of Prop 5.1 (1) and Prop 5.2 in Cremona and Najman's paper fails, and in the case Prop 5.1 (1) fails, it also returns the rational prime below. 
// 3) "No CM" - If the EC does not have CM and it has been unable to shown the EC is not a Q-curve. In particular, a non CM Q-curve will always give this output.

CMorQcurve:= function(j)
Ej := EllipticCurveFromjInvariant(j);
tf, D :=  HasComplexMultiplication(Ej);
if tf then return tf, D; end if;
K := Parent(j);
OK := Integers(K);
Fact := Factorisation(OK*j);
denomprimes :=[];

for pp in Fact do
if pp[2] lt 0 then
Append(~denomprimes,pp[1]);
end if;
end for;

primesbelow := {Characteristic(ResidueClassField(P)): P in denomprimes};

if #Seqset(denomprimes) lt #{P[1]: P in Factorisation(pp*OK), pp in primesbelow} then
return false, "multiplicative reduction condition fails";
end if;
BadRatPrimes := { Characteristic(ResidueClassField(Ideal(v))) : v in BadPlaces(Ej)};

for pp in PrimesInInterval(1,2000) do
if pp in BadRatPrimes then continue; end if;
if #{IsSupersingular(Reduction(MinimalModel(Ej,P[1]),P[1])): P in Decomposition(OK,pp)} eq 2 then
return false, "Supersingular condition fails for", pp;
end if;
end for;

return "No CM";

end function;
