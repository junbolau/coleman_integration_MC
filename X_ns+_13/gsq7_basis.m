load"zywina.m";

// specify the number of terms in the q-expansion
prec:= 5000;
K<zetaN> := CyclotomicField(13);
M<zeta39> := CyclotomicField(39);
Embed(K,M,zeta39^3);

a,b,c,d := SL2ActionOnCuspForms(13,2,prec: HNF := true);

//Construction of normaliser of nonsplit Cartan
Gsq7:= sub<GL(2,Integers(13))|[[1,7,1,1],[1,0,0,-1]]>;
basis7:= ComputeModularFormsForXG(Gsq7,2,prec);

f17:= Coefficients(basis7[1]);
f27:= Coefficients(basis7[2]);
f37:= Coefficients(basis7[3]);
Bsq7:= Matrix(3,prec,[f17,f27,f37]);

B:= ChangeRing(b,K);
Sol7:= Solution(B,Bsq7);
