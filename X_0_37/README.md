This folder contains the calculation of tiny integrals on the modular curve X_0(37) in Example 4.1.1.

- ```modpoly3.txt``` contains the coefficients of the modular polynomial at p=3. This is obtained from Drew Sutherland's database of modular polynomials.
- ```tiny_integrals.ipynb``` contains the calculations of tiny integrals.
- ```magma_coleman_integrals.m``` contains the magma code to calculate the Coleman integrals using the Magma implementation by Balakrishnan-Tuitman (https://github.com/jtuitman/Coleman).

The sum of tiny integrals are computed with our method using model, even though same results can be given by the model-free code with longer runtime.
