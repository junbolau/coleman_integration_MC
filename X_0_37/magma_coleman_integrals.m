// From https://github.com/jtuitman/Coleman
load "coleman.m";
f := y^2 -( -x^6 - 9*x^4 -11*x^2 + 37);
p := 3;
N := 15;

data := coleman_data(f,p,N);
Q := set_point(1,-4,data);
R := set_point(-1,-4,data);

// First two outputs are the integrals on holomorphic differentials, which agrees with our results
coleman_integrals_on_basis(Q,R,data);

