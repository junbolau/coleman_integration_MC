This is the folder for the computation of Coleman integrals on the modular curve defined by the normaliser of the nonsplit Cartan subgroup X_ns^+(13).

- ```zywina.m``` is a Magma file containing a slight modification of Zywina's implementation of computing the action of slash-k operators.
- ```modpoly11.txt``` is a text file containing the coefficients of the modular polynomial at p=11. This is obtained from Sutherland's database of modular polynomials.
- ```gsq7_basis.m``` is a Magma file based on ```zywina.m``` to compute a basis for the space of weight 2 cusp forms. This is saved in ```basis_zywina_Gsq7.sage```.
- ```hecke_action.m``` is a file containing the calculations to compute the matrix of the Hecke operators acting on the space of cusp forms.
- ```tiny_integral_computation.ipynb``` is the Jupyter notebook containing the calculations for a model-free Coleman integration.
