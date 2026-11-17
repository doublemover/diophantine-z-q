# Constructed finite binary congruences

Status: independently source-reviewed, not yet Lean-accepted. This is only the finite `cy:binary` ingredient, not the restricted converse or a point producer.

For each Boolean group element g, use the degree-one polynomial L_g(X)=sum_i g_i X_i over F2. Its evaluation is the parity of g·x. Reduce arbitrary integral coefficient c_g modulo 2^M to a nonnegative a_g, and repeat L_g exactly a_g times.

The explicit recursive coefficient P_k of product_L (1+Y L) has ordinary total degree at most k. At a Boolean point x, the product equals (1+Y)^(A(x)), where A(x) is the actual number of active forms, repetitions included. Thus eval_x(P_k)=choose(A(x),k) modulo 2. Native Lucas identifies the coefficient with k=2^j as the actual jth binary digit of A(x).

For r tests and j<M, these equations all vanish at x=0 and the sum of their degree bounds is r(2^M-1). The already existing Boolean-cube parity theorem, applied to product(1+P_ij), gives another common zero when this sum is less than b. Hence every A_j(x) is divisible by 2^M.

The exact integer identity sum_g a_g(-1)^(g·x) = sum_g a_g - 2A(x) transports these constructed count congruences to sign evaluations. Coefficientwise reduction transports from a_g back to arbitrary signed c_g. Finally, the native toZModPow map and its canonical finite residue representatives transport arbitrary actual Z_2 coefficients to this integral construction. No coefficient positivity, supplied digit polynomial, or supplied degree hypothesis remains in the final theorem.

This proof uses a generating product of repeated linear forms rather than the manuscript's weighted monomial expansion. Repetition does not affect the degree bounds or the dimension estimate. It is a finite proof, with no limiting or uniformity assertion beyond the stated coefficient-independent bound.

Remaining global work includes constructing the actual reduced-Sha pairing and its properties, the actual uniform global diagrams/paired functional in the missing-vertex argument, and the analytic-to-rational-point steps. None is inferred from the finite theorem.
