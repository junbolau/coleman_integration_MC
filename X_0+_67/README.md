This folder contains the calculations of Coleman integrals in Example 4.2.1.

- ```13.txt``` is the file containing coefficients of modular polynomial at p=13, obtained from Drew Sutherland's database of modular polynomials.
- ```model_free_67_R_ omega0.ipynb``` contains the calculations up to the computation of Taylor expansions.
- ```model_and_rational_points.ipynb``` contains the calculations of Coleman integrals using a hyperelliptic model of X_0^+(67).
- ```tiny_integrals_R.ipynb``` and ```tiny_integrals_S.ipynb``` contain calculations of tiny integrals at the two chosen points. Correctness of results can be verified in the first file.

The sum of tiny integrals are computed with our method using model, even though same results can be given by the model-free code with longer runtime.
