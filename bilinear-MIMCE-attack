clear;

// magma code to compute a bilinear system of equations to solve the MIMCE problem 

// ---------------- SET-UP FUNCTIONS ------------------

// random lower triangular matrix
GenLowerTriangular := function(k,q)
	F := FiniteField(q);
	M := ZeroMatrix(F,k);
	for i,j in [1..k] do 
		if i ge j then
			M[i][j] := Random(F);
		end if;
	end for;
	return M;
end function;

// random invertible symmetric matrix
GenSymInvMat := function(k,q)
	F := FiniteField(q);
	while true do 
		// add a lower triangular to its transpose and check if invertible
		T := GenLowerTriangular(k,q);
		M := T + Transpose(T);
		if Determinant(M) ne 0 then 
			return M;
		end if;
	end while;
end function;

// random invertible matrix
GenRandomInvertible := function(k,q)
	F := FiniteField(q);
	while true do 
		M := RandomMatrix(F,k,k);
		if Determinant(M) ne 0 then 
			return M;
		end if;
	end while;
end function;

 // random code (via its generator matrix)
GenCode := function(m,n,k,q)
	F := FiniteField(q);
	while true do 
		C := RandomMatrix(F,k,m*n);
		if Rank(C) eq k then 
			return C;
		end if;
	end while;
end function;

// generate an instance of MIMCE with 1 sample
GenMIMCE := function(m,n,k,q)
	G0 := GenCode(m,n,k,q);

	S0 := GenRandomInvertible(k,q);
	S1 := GenRandomInvertible(k,q);

	A := GenSymInvMat(m,q);
	B := GenSymInvMat(n,q);
	K := KroneckerProduct(A,B);

	G1 := S0 * G0 * K;
	G2 := S1 * G0 * K^-1;

	return G0,G1,G2;
end function;


// ---------------- ATTACK SUBROUTINES ------------------


// computes the parity check matrix given a generator matrix
ComputeParityCheck := function(G)
	m:=#Rows(G); // # of rows
	n:=#Rows(Transpose(G)); // # of columns
	Fp:=Parent(G[1][1]);

	// reduce matrix to rref and take non-identity segment
	M := EchelonForm(G);
	T := ExtractBlock(M,1,m+1,m,n-m);
	I := IdentityMatrix(Fp,n-m);
	H := HorizontalJoin(-1*Transpose(T),I);
	return H;
end function;


// ----------------- ATTACKS -------------------


// algebraic attack on MIMCE **BILINEAR VERION**
// No S0 variables
biMIMCE := function(m,n,k,q,G0,G1,G2)
	F := FiniteField(q);
	// vars for A
	sym_vars := Integers()!(m*(m+1)/2);
	// vars for A and S0
	poly<[X]> := PolynomialRing(F,2*sym_vars);

	H1 := ComputeParityCheck(G1);

	G0 := ChangeRing(G0,poly);
	G1 := ChangeRing(G1,poly);
	G2 := ChangeRing(G2,poly);
	H1 := ChangeRing(H1,poly);

	// construct A and B as a variable matrix to be solved for
	A := ZeroMatrix(poly,m);
	B := ZeroMatrix(poly,n);
	counter := 1;
	for i,j in [1..m] do 
		if i ge j then 
			A[i][j] := X[counter];
			A[j][i] := X[counter];
			B[i][j] := X[counter+sym_vars];
			B[j][i] := X[counter+sym_vars];
			counter +:= 1;
		end if;
	end for;

	mats := [];

	// ----------- relations for A and B but not S0 ---------------

	// R := G0*KroneckerProduct(A,B)*Transpose(H1);

	// ---- relations for A and B but not S0--using blocking approach -------

	P := G0* KroneckerProduct(A,B);

	// Separate P into blocks and store in a list
	Lvars := [];
	for i in [1..n] do 
		M := Submatrix(P,1,(i-1)*n+1,k,m);
		Lvars cat:= [M];
	end for;

	// separate G1 into blocks
	Lg0 := [];
	for i in [1..n] do 
		M := Submatrix(G1,1,(i-1)*n+1,k,m);
		Lg0 cat:= [M];
	end for;

	// add linear relations to list
	for j in [2..n] do
		T := Lvars[1]*Lg0[1]^-1 - Lvars[j]*Lg0[j]^-1;
		mats cat:= [T];
	end for;

	// // ---- relations for A and B but not S1--using blocking approach -------

	P := G2* KroneckerProduct(A,B);

	// Separate P into blocks and store in a list
	Lvars := [];
	for i in [1..n] do 
		M := Submatrix(P,1,(i-1)*n+1,k,m);
		Lvars cat:= [M];
	end for;

	// separate G1 into blocks
	Lg0 := [];
	for i in [1..n] do 
		M := Submatrix(G0,1,(i-1)*n+1,k,m);
		Lg0 cat:= [M];
	end for;

	// add linear relations to list
	for j in [2..n] do
		T := Lvars[1]*Lg0[1]^-1 - Lvars[j]*Lg0[j]^-1;
		// multiply by all of the S0 variables
		// mats cat:= [X[s]*T:s in [2*sym_vars+1..2*sym_vars+k^2]] cat [T];
		mats cat:= [T];
	end for;


	// ----------- solve relations in variety ----------------------

	// normalize one entry in each of A,B,S0
	eqs := [X[1] -1,X[sym_vars + 1]-1];
	for i in [1..m] do
		for j in [1..k] do 
			for M in mats do 
				eqs cat:= [M[i][j]];
			end for;
			// eqs cat:= [R[i][j]];
		end for;
	end for;

	SetVerbose("Groebner",false);
	// #eqs;
	I := Ideal(eqs);
	sols := Variety(I);

	// post process solutions back into matrix form
	cands := [];
	for s in sols do 
		counter := 1;
		A0 := ZeroMatrix(F,m);
		B0 := ZeroMatrix(F,m);
		for i,j in [1..m] do 
			if i ge j then 
				A0[i][j] := s[counter];
				A0[j][i] := s[counter];
				B0[i][j] := s[counter+sym_vars];
				B0[j][i] := s[counter+sym_vars];
				counter +:= 1;
			end if;
		end for;
		if Determinant(A0) ne 0 then
			cands cat:= [[A0,B0]];
		end if;
	end for;

	return cands;
end function;


// ------------------ testing one MIMCE --------------------

n := 2; m := n; k := n; q := NextPrime(1000);
"n = ", n;

"bilinear ";
for i in [1..1] do 
	G0,G1,G2 := GenMIMCE(m,n,k,q);
	time sols := biMIMCE(m,n,k,q,G0,G1,G2);
	#sols;
end for;
