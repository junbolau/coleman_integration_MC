load"zywina.m";

/*
This function uses Zywina's implementation to compute the action of slash_k operator in order to compute the Hecke matrix

Inputs:
p 	= level of nonsplit Cartan
ell 	= Hecke operator at ell
gens 	= list containing generators of (normaliser of) nonsplit Cartan, depending on conjugacy class
prec 	= precision
alpha_list = list containing matrices of length ell + 1, corresponding to the Hecke action

Functions:

*/

function HeckeAction(p,ell,gens,prec,alpha_list)
	K<zeta_p> := CyclotomicField(p);
	M<zeta_pell>:= CyclotomicField(p*ell);
	Embed(K,M,zeta_pell^ell);
	a,b,c,d := SL2ActionOnCuspForms(p,2,prec: HNF:=true);
	G := sub<GL(2,Integers(p))|gens>;
	basislist:= ComputeModularFormsForXG(G,2,prec);
	len := #basislist;
	B:= ChangeRing(b,K);

	sol_list := [Transpose(Solution(B,Matrix(K,1,prec,Coefficients(basislist[i])))) : i in [1..len]];
	alpha_matrices:= [ Transpose(d(Matrix(2,2,i))) : i in alpha_list ];

	q_exp_alpha_action_basis := [ [Transpose(alpha_i*sol_j)*B : alpha_i in alpha_matrices] : sol_j in sol_list] ; // a list q-exp of f_j | alpha_i

	v_ell_list := [[Matrix(1,prec,[bqexp[i][1][n]*zeta_pell^( (i-1)*n) : n in [1 .. prec]]) : i in [1..ell]] : bqexp in q_exp_alpha_action_basis];
	s_ell_list := [ (1/ell)*(&+lst) : lst in v_ell_list];	

	snew_list := [ [M!0 : n in [1.. Floor(prec/ell)]] : i in [1..len]];
	for j in [1.. len] do
		for i in [1.. Floor(prec/ell)] do
			snew_list[j][i] := s_ell_list[j][1][ell*i] ;
		end for;
	end for;


	s_ell_matrix := [ Matrix(1,Floor(prec/ell), snew) : snew in snew_list];
	
	ellplusone_list := [ [M!0 : n in [1.. Floor(prec/ell)]] : i in [1..len]];
	for j in [1.. len] do
		for i in [1.. Floor(prec/(ell^2))] do
			ellplusone_list[j][ell*i] := q_exp_alpha_action_basis[j][ell+1][1][i];
		end for;
	end for;

	ellplusone_matrix := [ Matrix(1, Floor(prec/ell), ellplusone) : ellplusone in ellplusone_list ];
	action_list := [ ChangeRing( s_ell_matrix[i] + ell*ellplusone_matrix[i],K) : i in [1..len] ];

	bound := Floor(prec/ell);
	
	BMat := Matrix(len, bound, [ Coefficients(basislist[i])[1 .. bound] : i in [1 .. len] ]);
	ImMat := Matrix(len, bound, [ [action_list[j][1][i] : i in [1 .. bound]] : j in [1 .. len] ] );

	HeckeMat:= Solution(BMat,ImMat); // HeckeMat*[f1,f2,f3]^T = ImMat

	return HeckeMat;
end function;




// Use this for our example with the following inputs:

p := 13;
ell := 11;
gens := [[1,7,1,1],[1,0,0,-1]];
prec := 300;
alpha_list := [[-13, 4, 42, -13], [-101, 4, 328, -13], [-13, -9, 42, 29], [-13, 69, 42, -223], [-13, -22, 42, 71], [-13, 56, 42, -181], [-13, -35, 42, 113], [-13, 43,42, -139], [-13, -48, 42, 155], [-13, 30, 42, -97], [13, 61, -42, -197], [650, 551, -2101, -1781]];

HeckeAction(p,ell,gens,prec,alpha_list);

