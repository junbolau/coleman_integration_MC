/*
   This is a very basic implementation of the algorithm from the paper "Computing actions on cusp forms" for computing the Atkin-Lehner operator on 
   spaces of cusp forms with integral weight k>1.   

   The main functions are the following (see the function in the code for detailed descriptions):
        "ComputeAtkinLehner"   : for a congruence subgroup Gamma between Gamma_1(N) and Gamma_0(N), computes a basis of S_k(Gamma,Z) given
                                 by their q-expansion and a matrix W that gives the action of the Atkin-Lehner operator W_N on S_k(Gamma) in terms of this basis.
        "SL2ActionOnCuspForms" : computes a basis of S_k(Gamma(N),Z) and gives the natural right action of SL_2(Z/NZ) on S_k(Gamma(N),Q(zeta_N))
                                 with respect to this basis.
        "FindCanonicalModel"   : for a subgroup G of GL(2,Z/NZ) with full determinant and containing -I, computes a set of generators of the homogeneous 
                                 ideal of the image of a canonical map X_G -> P^{g-1},  where X_G is the modular curve of genus g associated to G.
                                 This works well for small N but has not been optimized.
    
  Remarks on numerical computations:
  The only thing not fully implemented is working out the error terms in the numerical approximations. We simply compute everything to a much higher accuracy
  than is actually needed.  When rounding real numbers that should be integers, we use "AlmostEqual" to ensure that they are indeed close; our default setting 
  is within distance 0.0001 of each other.   When we finally compute the matrix W describing the Atkin-Lehner operation, we also verify that W^2 is the 
  appropriate scalar matrix
  In each of the above functions, there is a parameter "prec" which says how many terms of the q-expansions to compute. If not enough terms have been computed
  to distinguish cusp forms, the function is halted or an error is produced.   One could use the Sturm bound, but this is often much larger than required.

  The q-expansions are also used to compute the pseudo-eigenvalues of newforms; the series involved converge quickly so not that many terms are actually needed 
  in practice.    In our function for computing pseudo-eigenvalues, there is also a parameter b>0 that one is allowed to vary (we work with a fixed b that has 
  worked for all examples so far).    

  Some examples to try:

        _,B,W,_:=ComputeAtkinLehner(7^2,2,[1+7],100 : real:=true);
        B; W/7;  

        G:=sub<GL(2,Integers(13))|[ [2,0,0,2], [1,0,0,5], [0,-1,1,0], [1,1,-1,1] ]>;
        FindCanonicalModel(G,200);

        G:=sub<GL(2,Integers(17))|[ [1,2*3,2,1],[1,0,0,-1]]>;
        FindCanonicalModel(G,200);

        G:=sub<GL(2,Integers(9))| [[2,0,0,1],[1,0,0,2]]>;
        FindCanonicalModel(G,200);

*/

// We first fix the precision of the real numbers we work with.
RR:=RealField(50);   
SetDefaultRealField(RR);


function AlmostEqual(A,B: prec:=0.0001)
/* Input: A and B are complex matrices of the same size.
   Output: returns true if all the entries of A-B have absolute value less than "prec", otherwise returns false.
*/	
        b:= exists(d){ A[i,j]-B[i,j]: i in [1..Nrows(A)], j in [1..Ncols(A)] | AbsoluteValue(A[i,j]-B[i,j]) ge prec };
        if b then
		print "Matrices not \"almost equal\" :", d; 
	end if;
	return not b;
end function;

function PseudoEigenvalue(N,k,f: b:=1.1)
/* Input: f is the coefficients of a newform of integral weight k>1 and level N; starting at the coefficient of q.
   Output: the pseudo-eigenvalue of f; a complex number of absolute value 1.
   Note b is a positive real number used in the approximation 
*/       
	RR:=GetDefaultRealField(); b:=RR!b;
	w1:=Exp(-2*Pi(RR)/(b*Sqrt(RR!N)));
	w2:=Exp(-2*Pi(RR)*b/(Sqrt(RR!N)));

	s1:=&+[ f[n]*w1^n : n in [1..#f]];
	s2:=&+[ ComplexConjugate(f[n])*w2^n : n in [1..#f]];

	lambda:=s1/s2/b^k; 
        if IsEven(k) then
    	    lambda:=(-1)^(k div 2)*lambda; 
        else
            i:=Name(Parent(lambda),1);
            lambda:=i^k*lambda;
        end if;

        assert AbsoluteValue(AbsoluteValue(lambda)-1) lt 0.00001;  // check that lambda is reasonable (otherwise one should change b)
        return lambda;
end function;


function ComputeAtkinLehnerNewform(N,k,S0,prec)
	/* Input:
                N: a positive integer.	
                k: an integer at least 2.
                S0: an irreducible cuspidal subspace of weight k modular forms for Gamma_1(N) as produced by Magma's "NewformDecomposition".
                    This agrees with a space M_f as in the paper.
		prec: a positive integer to indicate how many terms of q-expansions to use for computations.

	   Output:
                g: dimension of S0.
		B: a matrix with integer entries whose rows give the first "prec" coefficients of the q-expansion of a basis of 
                   the Z-module S0(Z), where S0(Z) consists of cusp forms in S0 with integral coefficients.   It will be in Hermitian normal form.
		W: a matrix describing the action of the Atkin-Lehner involution W_N on S0 with respect to the basis coming from B.
                Q: minimal positive integer for which the entries of W lie in the Q-th cyclotomic field.
	*/
   
        //  The rows of the matrix B give the first "prec" terms of q-expansions of a basis of S0 in S0(Z).
        B:=Matrix([ [Coefficient(f,n):n in [1..prec]] : f in qIntegralBasis(S0,prec+1)]);
        g:=Nrows(B);

        // Make sure enough terms have been computed so that the rows of B are linearly independent
        if Rank(B) ne g then
            "Need to compute more terms of q-expansions."; assert false;
        end if;
     
        //  Due to the "qIntegralBasis" implementation, our matrix B will already be in Hermitian form. We find the pivots.
        pivot:=[ [j: j in [1..Ncols(B)]|B[i,j] ne 0][1] : i in [1..Nrows(B)]];  
        pivot_value:=[ B[i,pivot[i]] : i in [1..Nrows(B)]];


	// Compute q-expansion of newform corresponding f to S0 whose coefficients generate a number field L.
	f:=Eigenform(S0,prec+1);
	L:=BaseRing(Parent(f));    
	coeff:=[Coefficient(f,n): n in [1..prec]];
	epsilon:=DirichletCharacter(S0);   // Nebentypus of f.

        // Group of units UN:=(Z/NZ)^* with a sequence of generators in Z.
        UN,iota:=UnitGroup(Integers(N));
	Ugen:=[ Integers()!iota(UN.i): i in [1..Ngens(UN)] ];

   
	/* We now compute a matrix A whose rows are the coefficients of the newforms in S0 (more precisely, the first "prec" terms).
	   These are obtained by applying the complex embeddings of the field L to the coefficients of f.

	   We compute a matrix W, with complex entries, that describes the action of W_N on the basis encoded by A.
	   We also compute a sequence of matrices D that describes the action of the diamond operators of the integers in Ugen on the 
           basis encoded by A.  The matrices in D will all be diagonal.
        */

	// Archimedean places of L.
	PL:=InfinitePlaces(L);  PL1:=RealPlaces(L);

	A:=[];
	W:=[];
	D:=[ [] : m in [1..#Ugen]];

        RR:=GetDefaultRealField();  
        precR:=Precision(RR);
        CC<ii>:=ComplexField(RR);

	e:=[ epsilon(m) : m in Ugen ];
        NN:=(RR!N)^(k/2);

	for v in PL do
		c :=[CC!Evaluate(coeff[i],v :Precision:=precR) : i in [1..prec]];  
		c_:=[ComplexConjugate(a): a in c];
		lambda:=PseudoEigenvalue(N,k,c);

		if v notin PL1 then
			A:=A cat [c] cat [c_];
			W:=W cat [ Matrix([[0,(-1)^k*NN*lambda ], [NN*lambda^(-1),0]]) ];
                        for i in [1..#Ugen] do
                            ev:=CC!Evaluate(e[i],v :Precision:=precR);
                            D[i]:= D[i] cat [ev,ComplexConjugate(ev)];
                        end for;
                else
			A:=A cat [c];
			W:=W cat [ Matrix([[(-1)^k*NN*lambda]]) ];
                        for i in [1..#Ugen] do
                            ev:=CC!Evaluate(e[i],v :Precision:=precR);
                            D[i]:= D[i] cat [ev];
                        end for;
		end if;            
	end for;
	A:=Matrix(A);
	W:=DiagonalJoin(W);
        D:=[DiagonalMatrix(D[i]): i in [1..#Ugen]];


        // We change the Atkin-Lehner and diamond operator matrices W and D to be with respect to the basis B.
        // We do this by first finding the matrix P satisfying P*B = A.  The following uses that B is in Hermitian form.

        P:=[];
        RowsB:=Rows(ChangeRing(B,CC));
        for r0 in Rows(A) do
            v:=r0;
            row:=[];
            for i in [1..Nrows(B)] do
                a:=v[pivot[i]]/pivot_value[i];
                row:=row cat [a];
                v:=v-a*RowsB[i];
            end for;
            P:=P cat [row];
         end for;
         P:=Matrix(P); P_inv:=P^(-1);
	 D:=[P_inv*D[i]*P: i in [1..#Ugen]];
	 W:=P_inv*W*P;  

	// The matrices of D will now have integer entries; we coerce them.
	D_:=[];
	for e in [1..#Ugen] do
		C_:=Matrix([[Round(Real(D[e][i,j])): j in [1..Ncols(D[e])]]: i in [1..Nrows(D[e])] ]);
		almostequal:=AlmostEqual(D[e],C_);
		if not almostequal then "Diamond operators not integral"; D[e]; assert almostequal; end if;                  
		D_:=D_ cat [C_];
	end for;
	D:=D_;

	// We now find the minimal Q such that the diamond operators map through (Z/QZ)^*.
	// This Q is also be the minimal positive integer for which the entries of W will lie in the Q-th cyclotomic field.

	diamond0:=hom<UN->GL(g,Integers()) | D>;
	for d in Sort([d: d in Divisors(N)]) do
		if &and[Order(diamond0((1+d*b) @@ iota)) eq 1  : b in [1..N div d] | GCD(1+d*b,N) eq 1] then
			Q:= d; break;
		end if;
	end for;

        // UQ is the group of units of Z/QZ and phi is the reduction map from UN to UQ.
	UQ,iotaQ:=UnitGroup(Integers(Q));
	phi:=hom<UN->UQ|[ (Integers(Q)!(Integers()!iota(UN.i))) @@ iotaQ : i in [1..#Generators(UN)]]>;
	diamondop:=hom<UQ->GL(g,Integers()) | [diamond0(UQ.i @@ phi) : i in [1..#Generators(UQ)]]>;

        // Given an integer a relatively prime to Q, computes the action of the diamond operator <a> on S0 wrt basis B.
	function diamond(a)   return diamondop(a @@ iotaQ);  end function;
	 
        // We now determine the matrix W exactly; it has entries in the Q-th cyclotomic field.      
	K<zetaQ>:=CyclotomicField(Q);  xi:=zetaQ;
    	d:=AbsoluteDegree(K);

        // For c in Q^d, the following function computes the unique x in K such that Tr_{K/Q}( xi^(i-1)*x )=c_i for all i=1,..,d.
    	C:=Matrix([[ Trace(xi^(i-1)*xi^(j-1)) : j in [1..d]] : i in [1..d] ])^(-1);
    	function DetermineFromTraces(c)  
		if #c eq 1 then return c[1]; end if;
		b:=Eltseq(Vector(c)*C);
		return &+[b[i]*xi^(i-1): i in [1..d]];
	end function;

        // We now apply the main algorithm of the paper.
        BB:= &*(pivot_value cat [p^Ceiling(k/(p-1)): p in PrimeDivisors(N)]);   
        zeta:=Exp(2*Pi(CC)*ii/Q);
        TT:=[];
	for b in [0..d-1] do
		beta:=BB * W * &+[ (zeta^a)^b * Parent(W)!diamond(a) : a in [1..Q] | GCD(Q,a) eq 1];
		beta_:=Matrix([ [Round(Real(beta[i,j])): j in [1..Ncols(beta)]] : i in [1..Nrows(beta)]]);                                

                assert AlmostEqual(beta,beta_); // Cannot determine matrices; should increase "prec".               
		TT:=TT cat [ChangeRing(beta_,Rationals())/BB];
	end for;       
	W:=Matrix([[ DetermineFromTraces([TT[e][i,j]: e in [1..#TT]]) : j in [1..g]] : i in [1..g] ]);
        
        // Check that W^2 is the appropriate diagonal matrix.  If the numerical approximations were not accurate enough, then
        // this will almost surely fail. 
        assert W^2 eq N^k*Parent(W)!(-1)^k;  

	return g,B,W,Q;
end function;

function VerticalJoin0(B)
   if #B eq 0 then return []; end if;  A:=B[1]; for i in [2..#B] do A:=VerticalJoin(A,B[i]); end for; return A;
end function;

function DiagonalJoin0(B)
   if #B eq 0 then return []; end if; A:=B[1]; for i in [2..#B] do A:=DiagonalJoin(A,B[i]); end for; return A;
end function;

function ComputeAtkinLehnerNewspace(N,k,gen,prec)
/* Input: N: a positive integer. 
          k: a positive integer at least 2.
          gen: a sequence of integers that are relatively prime to N.
	  prec: a positive integer to indicate how many terms of a q-expansion to use for computations.
 
   Let H be the subgroup of the units of Z/NZ generated by "gen".    Let Gamma_H be the congruence subgroup of level N whose image modulo N
   consists of upper triangular matrices whose diagonal entries lie in H.
   Let S be the newspace of cusp forms in S_k(Gamma_H).
   
   Output: g: the dimension of S.
           B: a matrix with integer entries that describes a basis of S.  Each row give the first "prec" coefficients of a q-expansion.
           W: g by g matrix that describes the action of the Atkin-Lehner operator W_N with respect to the matrix given by B.
           Q: the smallest positive integer for which the diamond operators <a> acting on S depend only on a mod Q.  
*/
	S:=NewSubspace( CuspidalSubspace(ModularSymbolsH(N,gen,k,+1)) );
	if Dimension(S) eq 0 then return 0,[],[],1; end if;

	B:=[* *]; W:=[* *]; Q:=1;
	for S0 in NewformDecomposition(S) do  
		_,B0,W0,Q0 := ComputeAtkinLehnerNewform(N,k,S0,prec);
		B:=B cat [*B0*];  W:=W cat [*W0*];  Q:=LCM(Q,Q0);
	end for;	
        B:=VerticalJoin0(B);
	W:=DiagonalJoin0([* ChangeRing(A,CyclotomicField(Q)): A in W *]);

        // Make sure enough terms have been computed so that the rows of B are linearly independent
        if Rank(B) ne Nrows(B) then
           "Need to compute more terms of q-expansions.  Increase prec"; assert false;
        end if;

	return Nrows(B), B, W, Q;
end function;


function ComputeAtkinLehner(N,k,gen,prec : real:=false, HNF:=true)

/* Input: N: a positive integer.
          k: a positive integer at least 2.
          gen: a sequence of integers that are relatively prime to N.
	  prec: a positive integer to indicate how many terms of a q-expansion to use for computations.
 
   Let H be the subgroup of the units of Z/NZ generated by "gen".    Let Gamma_H be the congruence subgroup of level N whose image modulo N
   consists of upper triangular matrices whose diagonal entries lie in H.
   
   Output: g: the dimension of S_k(Gamma_H).
           B: a matrix with integer entries that gives a basis of S_k(Gamma_H).  
              Each row give the first "prec" coefficients of a q-expansion.
           W: g x g matrix that describes the action of the Atkin-Lehner operator W_N with respect to the matrix given by B.
           Q: the smallest positive integer for which the diamond operators <a> acting on S_k(Gamma_H) depend only on a mod Q.  

           If "real" is false, then the entries of W are returned in the Q-th cyclotomic field Q(zetaQ).
           If "real" is true and k is even, then the entries of W are returned in Q(xi), where xi:=zetaQ+1/zetaQ.

           If "HNF" is true, then the rows of B give rise to a basis of the Z-module S_k(Gamma_H,Z) and B is in Hermitian normal form.  
           When HNF is false, we use B coming from Atkin-Lehner-Li theory which often produces a matrix W with many zero entries.
*/

    B:=[* *]; W:=[* *]; Q:=1;
    for M in Divisors(N) do
        g0,B0,W0,Q0:=ComputeAtkinLehnerNewspace(M,k,gen,prec);
        if g0 eq 0 then continue M; end if;

        Z0:=ZeroMatrix(BaseRing(B0),Nrows(B0),Ncols(B0));
        Z1:=ZeroMatrix(BaseRing(W0),Nrows(W0),Ncols(W0));
        Q:=LCM(Q,Q0);

        for d in Divisors(N div M) do
            e:= (N div M) div d;
            if d gt e then continue d; end if;

            Bd:=Z0; Be:=Z0;
            for i in [1..Nrows(Bd)], j in [1..Ncols(Bd) div d] do
                Bd[i,d*j]:=B0[i,j];  
            end for;            
            for i in [1..Nrows(Be)], j in [1..Ncols(Be) div e] do
                Be[i,e*j]:=B0[i,j];
            end for;  
         
            if d eq e then
                W:=W cat [* d^k*W0 *];
                B:=B cat [* Bd *];
                continue d;
            end if;

            W1:=VerticalJoin(HorizontalJoin(Z1,e^k*W0),HorizontalJoin(d^k*W0,Z1));
            W:=W cat [* W1 *];            
            B:=B cat [* Bd, Be *];        
        end for;
    end for;

    if #B eq 0 then
        return 0, [], [], 1;
    end if;
    B:=VerticalJoin0(B);

    // Make sure enough terms have been computed so that the rows of B are linearly independent
    if Rank(B) ne Nrows(B) then
       "Need to compute more terms of q-expansions.  Increase prec."; assert false;
    end if;


    K<zetaQ>:=CyclotomicField(Q);
    W:=DiagonalJoin0([* ChangeRing(A,K) : A in W *]);
    if real and IsEven(k) then
       L<xi>:=sub<K|zetaQ+1/zetaQ>;
       W:=ChangeRing(W,L);
    end if;

    if HNF then
        // Replaces B, and updates W, so that the rows of B are a basis of the Z-module S_k(Gamma_H,Z).
        Bsat:=Saturation(B);
        M:=RSpaceWithBasis(Rows(Bsat));
        U:= Matrix([Coordinates(M,r) : r in Rows(B)]);
        U:=ChangeRing(U,Rationals());

        W:=U^(-1)*W*U; 
        B:=Bsat; 
  
        // Replaces B, and updates W, so that B is in Hermitian form.
        B1,U  :=HermiteForm(Bsat);
        W:=U*W*U^(-1);
        B:=B1;
    end if;

    return Nrows(B),B,W,Q;
end function;


function  SL2ActionOnCuspForms(N,k,prec : HNF:=false)
/* Input: N: a positive integer at least 2.
          k: a positive integer at least 2.
	  prec: a positive integer to indicate how many terms of a q-expansion to use for computations.

    Output:
          g: dimension of S_k(Gamma(N),Z).
          B: a matrix with integer entries that describes a basis of S_k(Gamma(N)); each row give the first "prec" coefficients of a q-expansion.
          M: with respect to the basis B, M is the right K[SL(2,Z/NZ)]-module S_k(Gamma(N),Q(zeta_N)).
          phi: the homomorphism SL(2,Z/NZ) -> GL_g( Q(zeta_N) ) corresponding to M with respect to the basis B. 

          If "HNF" is true, then the rows of B give rise to a basis of the Z-module S_k(Gamma_H,Z) and B is in Hermitian normal form.  
          When HNF is false, we use B coming from Atkin-Lehner-Li theory which is ofter preferable since phi will typically be defined in terms
          of matrices that are sparser.
*/

    g,B,W,Q:=ComputeAtkinLehner(N^2,k,[1+N],prec: HNF:=HNF);
    if g eq 0 then 
        return 0, [],[],[];
    end if;

    K<zetaN>:=CyclotomicField(N);

    // W is the matrix phi([0,-1; 1,0]).
    W:=ChangeRing(W,K)/N^k;

    // T is the matrix phi([1,1; 0,1]).
    T:=[];   
    RowsB:=Rows(ChangeRing(B,K)); 
    M:=RSpaceWithBasis(RowsB);
    for r in RowsB do
        m:=Eltseq(r);
        m:=M![ zetaN^n*m[n]: n in [1..#m] ];
        T:=T cat [Coordinates(M,m)];
    end for;
    T:=Matrix(T);

    SL2:=sub<SL(2,Integers(N)) | [[0,-1,1,0],[1,1,0,1]]>;  
    M:=GModule(SL2, [W,T]); 
    phi:=GModuleAction(M); 

    return g, B, M, phi;
end function;


function  ComputeModularFormsForXG(G,k,prec)
/* Input: G: a subgroup of GL(2,Z/NZ) with full determinant and contains -I with N>1.
          k: a positive integer at least 2.
	  prec: a positive integer to indicate how many terms of a q-expansion to use for computations.
    Output:
          The output is a sequence giving a basis for the Z-submodule of S_k(Gamma(N),Q(zeta_N))^G consisting of cusp forms 
          with coefficients in Z[zeta_N].
          Each cusp form is given by a sequence that gives the first "prec" coefficients of a q-expansion.
*/

    N:=#BaseRing(G);
    K<zetaN>:=CyclotomicField(N);
    OK:=RingOfIntegers(K);
    GL2:=GL(2,Integers(N));
    SL2:=sub<SL(2,Integers(N)) | [[0,-1,1,0],[1,1,0,1]]>; 
    H:=G meet SL2;

    // We first compute W:=S_k(Gamma(N),Q(zeta_N))^H.   It is a Q-vector space with a natural right G/H action.

    _, B, M, phi:=SL2ActionOnCuspForms(N,k,prec);
    MH:=Restriction(M, H);
    W:=Fix(MH);

    g:=Dimension(W);
    if g eq 0 then return []; end if;

    function ActionOfG(w,A)
        // For w in MH = S_k(Gamma(N),Q(zeta_N))^H and A in G, computes w*A.
        d:=Integers()!Determinant(A);
        h:= SL2!( A*(GL2![1,0,0,d])^(-1) );
        w:=M!(MH!w); 
        w:=w*h;
        w:=M![Conjugate(a,d): a in Eltseq(w)];             
        w:=W!(MH!w);
        return w;
    end function;

    // We now compute a basis F of S_k(Gamma(N),Q(zeta_N))^G;  equivalently, we find the subspace of 
    // W=S_k(Gamma(N),Q(zeta_N))^H fixed by G/H.   We choose our basis to have integral coefficients.

    UN,iota:=UnitGroup(RingOfIntegers(N));
    S:=[];
    for u in {Integers(N)!iota(u): u in Generators(UN)} do 
        _:=exists(A){A: A in G | Determinant(A) eq u};
        S:=S cat [A];
    end for;
    TT:=[];
    for A in S do    
        T:=[];
        for f in Basis(W) do
            w:=ActionOfG(f,A);
            d:=Integers()!Determinant(A);
            for i in [0..EulerPhi(N)-1] do
                T:=T cat [ &cat[ Eltseq(a): a in Eltseq(zetaN^(i*d)*w) ] ];
            end for;           
        end for;
        TT:=TT cat [Matrix(T)];  
     end for;

     d:=Dimension(W)*EulerPhi(N);
     R:=MatrixAlgebra(Rationals(),d);
     V0:=&meet[ Kernel(R!T-R!1) : T in TT ];  

     alpha:=[];
     for v0 in Basis(V0) do
         v:=Eltseq(v0);
         a:=[K![v[(j-1)*EulerPhi(N)+i]: i in [1..EulerPhi(N)]] : j in [1..Dimension(W)] ];
         alpha:=alpha cat [M!(MH!(W!a))];
     end for;

     R<q>:=PowerSeriesRing(K);
     BB:=[ &+[B[i,j]*q^j : j in [1..prec]] +O(q^(prec+1)) : i in [1..Nrows(B)] ];

     F:=[];
     for f in alpha do
         w:=Eltseq(f);  
         c:=LCM([Denominator(b) : b in &cat[Eltseq(a):a in w]]);  // smallest positive integer c such that c*w has entries in "OK".
         F:= F cat [ &+[c*w[i]*BB[i]: i in [1..#BB]] ]; 
     end for;

     // We now compute a basis F of the Z-module S_k(Gamma(N),Z[zeta_N])^G.

     B:=Matrix([ &cat[ Eltseq( Coefficient(F[i],j) ): j in [1..prec] ] : i in [1..#F] ]);
     B:=Saturation(B);
     B:=HermiteForm(B);
     F:=[ &+[ K![B[i,n*EulerPhi(N)+r+1] : r in [0..EulerPhi(N)-1]] * q^(n+1)  :  n in [0..Ncols(B) div EulerPhi(N) -1] ] + O(q^(prec+1))  : i in [1..Nrows(B)] ];

     return F;
end function;


function FindCanonicalModel(G,prec :ReturnBasis:=false)
/* Input: G: a subgroup of GL(2,Z/NZ) with full determinant and contains -I with N>1.
	  prec: a positive integer to indicate how many terms of a q-expansion to use for computations.
    Output:
        g: the genus g of X_G.
        psi: a set of generator of the homogeneous ideal of the image of a canonical map X_G -> P^{g-1}_Q.   
        If "ReturnBasis" is true, then we also return a basis f_1,..,f_g of S_k(Gamma(N),Q(zeta_N))^G such that F(f_1,...,f_g)=0 for all F in psi.      
*/
    N:=#BaseRing(G);
    F:=ComputeModularFormsForXG(G,2,prec);
    g:=#F;
    Pol<[x]>:=PolynomialRing(Rationals(),g);

    if g le 2 then 
        if ReturnBasis then return g, [], F; else return g, []; end if;
    end if;

    function ComputeId(F,d)
        // Compute a basis for I_d; the d-th graded component of the ideal I of the canonical curve.
        mon:=[m: m in MonomialsOfWeightedDegree(Pol,d)];
        C:=[Evaluate(f,F):f in mon];
        C:=[ &cat[Eltseq(Coefficient(f,n)): n in [1..prec]]: f in C];
        C:=ChangeRing(Matrix(C),Integers());
        L:=Kernel(C); 
        L:=Matrix(Basis(L)); 
        L:=LLL(L);
        psi:=[ &+[L[i,j]*mon[j]: j in [1..#mon]] : i in [1..Nrows(L)] ];
        return psi;
    end function;
       
    I2:=ComputeId(F,2);
    if  #I2 eq (g-1)*(g-2) div 2 then 
        print "XG is hyperelliptic"; 
        return g, I2; 
    end if;
    assert #I2 eq ((g-2)*(g-3)) div 2;
    print "XG is not hyperelliptic";

    if g eq 3 then
        I4:=ComputeId(F,4); f:=I4[1];
 
        // We have a model of X_G as a plane quartic with integer coefficients given by f=0.
        // We can use a built in Magma function to choose a nicer f.
        PZ<[x]>:=PolynomialRing(Integers(),#F);
        f,A:=MinimizeReducePlaneQuartic(PZ!f); 
        A:=A^(-1);
        F:=[ &+[A[i,j]*F[j]: j in [1..3]] : i in [1..3] ];

        if ReturnBasis then return g, [f], F; else return g, [f]; end if;
    end if;

    mon3:=[m: m in MonomialsOfWeightedDegree(Pol,3)];
    V:=VectorSpace(Rationals(),#mon3);
    W:=sub<V| [V![MonomialCoefficient(x[i]*f,m): m in mon3] : i in [1..g], f in I2]>;

    if Dimension(W) eq (g-3)*(g^2+6*g-10) div 6 then
        if ReturnBasis then return g, I2, F; else return g, I2; end if;
    end if;
    assert Dimension(W) eq ((g-3)*(g^2+6*g-10) div 6) - (g-3);

    I3:=ComputeId(F,3);
    V3:=sub<V| [V![MonomialCoefficient(f,m): m in mon3] : f in I3]>;

    J:=[];
    i:=1;
    while Dimension(W) lt Dimension(V3) do
        v:=V![MonomialCoefficient(I3[i],m): m in mon3];
        if v notin W then 
            W:=sub<V|Generators(W) join {v}>; 
            J:=J cat [I3[i]];
        end if;
        i:=i+1;
    end while;
    psi:=I2 cat J;

    if ReturnBasis then return g, psi, F; else return g, psi; end if;
end function;



