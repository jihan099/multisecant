-- This is an auxiliary code for the paper "Linear syzygies and linear subspaces whose lines are multisecant" by Jong In Han and Sijong Kwak.

-- Input: An homogeneous ideal of a polynomial ring whose generators
-- are d-forms satisfying N_d,2.
-- Output: The matrix M' that is internally used in other functions.
getMprime = I -> (
    syzI := syz gens I;
    S := ring I;
    s := (numgens I) - 1;
    R := (coefficientRing S)[globalVar_0 .. globalVar_s];
    Mprime := matrix table(numColumns syzI, numgens S, (i,j) -> sum(
    apply(s+1, k -> coefficient(S_j, syzI_(k,i)) * globalVar_k)));
    return Mprime;
)
-- Input: An homogeneous ideal of a polynomial ring whose generators
-- are d-forms satisfying N_d,2.
-- Output: The matrix M stated in Theorem A.
getM = I -> sub(getMprime I, gens I);

-- Input: I = An homogeneous ideal of a polynomial ring whose generators
-- are d-forms satisfying N_d,2 that defines a projective variety X
-- scheme-theoretically.
-- k = An integer.
-- Output: An ideal that defines the union of S_{k,d}(X) and X set-theoretically.
getEqn = (I, k) -> (
    r := (numgens ring I) - 1;
    J1 := trim minors(r+1-k, getMprime I);
    J2 := trim sub(J1, gens I);
    return J2;
)

-- Input: I = An homogeneous ideal of a polynomial ring whose generators
-- are d-forms satisfying N_d,2 that defines a projective variety X
-- scheme-theoretically.
-- k = An integer.
-- Output: A boolean value which is true if it passes the test
-- rank(M(p)) < r+1-k for three arbitrary points in the projective space.
-- If it returns false, then the result is deterministic.
isFull = (I, k) -> (
S := ring I;
r := (numgens S) - 1;
M := getM I;
for i from 1 to 3 do (
        p := matrix table(1, r+1, (i,j) -> random(0,S));
        if rank sub(M,p) >= r+1-k then return false;
    );
    return true;
)

-- Input: I = An homogeneous ideal of a polynomial ring
-- Output: A boolean value which is true if the scheme defined by I is normal
needsPackage "IntegralClosure"
isnormalsch = I -> (
    k := coefficientRing ring I;
    J := 0;
    for i from 0 to (numgens ring I)-1 do(
        J = sub(I,(ring I)_i=>1);
        J=sub(J,k[first entries submatrix'(vars ring I, ,{i})]);
        if J !=0 and J != (ideal 1_(ring J)) and isNormal((ring J)/J)==false then return false;
    );
    return true;
)

-- Input: list of integers a_1, ..., a_n
-- Output: the ideal of the rational normal scroll S(a_1, ..., a_n)
RNS = L -> (
	n:=sum L + #L - 1;
	S:=QQ[x_0..x_n];
	M:=matrix table(2,L_0,(i,j)->x_(i+j));
	lastInd := L_0+1;
	for i from 1 to #L -1 do (
		M=M|matrix(table(2,L_i,(i,j)->x_(i+j+lastInd)));
		lastInd = lastInd + L_i + 1;
	);
	return trim minors(2,M);
);


-- Example 3.6
<< "Example 3.6: " << endl;
S=QQ[x_0..x_4];
r=numgens S - 1;
M=matrix{{x_0..x_3},{x_1..x_4}}
I=minors(2,M);
<< "generators of I: " << endl;
gens I
<< "generators of syzygies: " << endl;
syz gens I
<< "M = " << endl;
getM(I)
needsPackage "PhylogeneticTrees";
<< "the ideal of secant: " << endl;
secant(I,2)
<< "isSame: " << secant(I,2) == radical(getEqn(I,1)) << endl;


-- Example 3.7
<< "Example 3.7: " << endl;
S=QQ[x_0..x_3];
r=numgens S - 1;
Q=x_1*x_2-x_0*x_3;
C_1=x_2^3-x_1*x_3^2;
C_2=x_0*x_2^2-x_1^2*x_3;
C_3=x_1^3-x_0^2*x_2;
I = ideal(Q,C_1,C_2,C_3);
<< "Betti table of I_X: " << endl;
print betti res I;
J=ideal(x_0*Q,x_1*Q,x_2*Q,x_3*Q,C_1,C_2,C_3);
<< "Betti table of J: " << endl;
print betti res J;
<< "S_{1,3}(X) union X: " << endl;
radical(getEqn(J,1))


-- Example 3.8
<< "Example 3.8: " << endl;
k=QQ;
S=k[x,y,z];
I1=ideal(x,y);
I2=ideal(y,x-z);
I3=ideal(y,x-2*z);
I4=ideal(x,y-z);
I5=ideal(x-z,y-z);
I6=ideal(x,y-2*z);
<< "ideal of points: " << endl;
I = trim intersect(I1,I2,I3,I4,I5,I6)
<< "decomposition: " << endl;
decompose getEqn(I,1)


-- Example 3.9
<< "Example 3.9: " << endl;
k=QQ;
S=k[x,y,z];
I1=ideal(x^3,y);
I2=ideal(x-z);
<< "I_X = " << endl;
I = trim intersect(I1,I2)
<< "Betti table of I_X: " << endl;
print betti res I;
d=first degree I_(numgens I-1);
gensI=first entries gens I;
while true do(
    for i in gensI do(
        if first degree i==d then continue
        else (
            gensI=delete(i,gensI);
            gensI=join(gensI,first entries (i*(vars S)));
        );
    );
    flag=true;
    for i in gensI do(
        if first degree i!=d then (
            flag=false;
            break;
        );
    );
    if flag==true then break;
);
<< "J = " << endl;
J = trim ideal gensI
<< "Betti table of J: " << endl;
print betti res J;
S4=getEqn(ideal gens J,1);
<< "Irreducible decomposition of S_{1,4}(X) union X: " << endl;
decompose S4


-- Example 5.7
<< "Example 5.7: " << endl;
S=QQ[x_0..x_11];
r=numgens S - 1;
I=trim minors(3,genericMatrix(S,3,4));
<< "I_3(M)=" << endl;
I3M = getEqn(I,r+1-3)
-- The below checks V(I_3(M))==X
isEqual = true; -- true if V(I_3(M))==X
for i from 0 to numgens I - 1 do (
    if radicalContainment(I_i,I3M) == false then (
        isEqual = false;
        break;
    );
);
<< "Is V(I_3(M))==X: " << isEqual  << endl;


-- Example 5.8
<< "Example 5.8: " << endl;
S=QQ[x_0..x_9];
r=numgens S - 1;
I=trim Grassmannian(1,4,S)
print betti res I;
<< "I_5(M)=" << getEqn(I,r+1-5) << endl;
I4M = getEqn(I,r+1-4);
<< "I_4(M)=" << endl;
I4M
<< "Is V(I_4(M))==X: " << radical(I4M)==I  << endl;


-- Example 5.9
<< "Example 5.9: " << endl;
<< "ideal of S(2,3) = " << endl;
I = RNS({2,3})
S = ring I;
r = numgens S - 1;
I2 = trim secant(I,2);
<< "(sigma_2X)_sing = " << endl;
sing = trim ideal singularLocus I2;
decompSing = decompose sing
<< "Is the second component same to the ideal of S(2,3): " << decompSing_1 == I << endl;
-- The below checks (S_{2,2}(X) cup X) == (sigma_2(X))_sing
S22 = getEqn(I,2);
isEqual = true; -- true if (S_{2,2}(X) cup X) == (sigma_2(X))_sing
-- Note that we only need to check that S_{2,2}(X) cup X is contained in (sigma_2(X))_sing since (sigma_2(X))_sing=V(x_3,x_4,x_5,x_6) cup X is contained in S_{2,2}(X) cup X.
for i from 0 to numgens sing - 1 do (
    if radicalContainment(sing_i,S22) == false then (
        isEqual = false;
        break;
    );
);
<< "Is (S_{2,2}(X) cup X) = (sigma_2(X))_sing: " << isEqual << endl;


-- Example 6.2
<< "Example 6.2: " << endl;
S=QQ[x_0..x_5];
R=QQ[y_0..y_3];
s_0 = y_0*y_1*y_3;
s_1 = y_0^2*y_2;
s_2 = y_0*y_2^2;
s_3 = y_0^2*y_1;
s_4 = y_0*y_1^2 + y_2^2*y_3;
s_5 = y_0^2*y_3 + y_2*y_3^2;
f = map(R,S,for i from 0 to 5 list s_i);
I = trim kernel f;
print betti res I;
<< "deg X = " << degree I << endl;
<< "set-theoretic eqns of (S_{1,4}(X) union X) = " << endl;
S41 = getEqn(I,1)
<< "dim (S_{1,4}(X) union X) = " << dim S41 - 1 << endl;
<< "dim X_sing = " << dim singularLocus I - 1 << endl;
<< "V(X_sing) = " << endl;
decompose ideal singularLocus I
<< "isNormal = " << isnormalsch I << endl;
<< "Is (S_{1,4}(X) != P5): " << not isFull(I,1) << endl;
<< "Is [1,1,1,1,1,1] a certificate point: " << sub(S41,sub(matrix{{1,1,1,1,1,1}},S)) != ideal(0_S) << endl;
-- To check S_{1,4}(X) cup X = S_{2,4}(X) cup X
isEqual = true;
S42 = getEqn(I,2);
for i from 0 to numgens S42 - 1 do (
    if radicalContainment(S42_i,S41) == false then (
        isEqual = false;
        break;
    );
);
for i from 0 to numgens S41 - 1 do (
    if radicalContainment(S41_i,S42) == false then (
        isEqual = false;
        break;
    );
);
<< "Is S_{1,4}(X) cup X = S_{2,4}(X) cup X:" << isEqual << endl;


-- Example 6.3
<< "Example 6.3: " << endl;
S=QQ[x_0..x_7];
R=QQ[y_0..y_4];
s_0 = y_0*y_2^2;
s_1 = y_2*y_3*y_4;
s_2 = y_1^3;
s_3 = y_0*y_2*y_4;
s_4 = y_1*y_2*y_3;
s_5 = y_1^2*y_2;
s_6 = y_2^2*y_4;
s_7 = y_0*y_1*y_2 + y_3^2*y_4;
f = map(R,S,for i from 0 to 7 list s_i);
I = trim kernel f;
print betti res I;
<< "deg X = " << degree I << endl;
<< "set-theoretic eqns of (S_{1,3}(X) union X) = " << endl;
S31 = getEqn(I,1)
<< "dim (S_{1,3}(X) union X) = " << dim S31 - 1 << endl;
<< "dim X_sing = " << dim singularLocus I - 1 << endl;
<< "V(X_sing) = " << endl;
decompose ideal singularLocus I
<< "isNormal = " << isnormalsch I << endl;
<< "Is (S_{1,3}(X) != P7): " << not isFull(I,1) << endl;
<< "Is [1,1,1,1,1,1,1,1] a certificate point: " << sub(S31,sub(matrix{{1,1,1,1,1,1,1,1}},S)) != ideal(0_S) << endl;
