# Actual nonseparable-weight minor integral via integrated Abel

All 1270 predecessor Lean sources are exact. Eight new sources, 461 lines, give 1278 total. No local Lean/profiling or changed caps. Hosted kernel validation and distinct source review remain pending.

The full original smooth minorArcIntegral now has the genuine four-moment/one-supremum bound, with produced W-dependent constants:

||minorArcIntegral(kappa,N,B,W)|| <= C*(2R+3)^5 * sqrt(minorQuadraticBudget(-kappa,H,N,ceil(B²/N))) * momentBudget(H,delta),
H=toNat(ceil(RB)), R>=1, C>=0, kappa!=0, N>0, B>=1, (N+1)^3<=B, delta>0.

The new integrated multiaxis Abel theorem keeps every terminal and mixed-difference term. Its hypothesis controls each JOINT phase-prefix integral separately, with its actual integrability witness. It never exchanges integral and maximum or pays five independent pointwise suprema. Smooth compact support directly produces mixed constants for the original unpaired W(x/B), not the previously used paired correlation weight. The actual five quadratic prefix products satisfy the joint condition by r17, including zero-length prefixes. Only the quadratic phase is factored; W remains one arbitrary function of all five coordinates.

Finally, the exact weighted time-rectangle identity and canonical compact support identify the bound with the literal full original minorArcIntegral. No supplied supremum, mixed weight budget or finite support remains in that final theorem.

Open: prove compatible quantitative N/B/divisor-exponent choices and normalized decay, then connect other arithmetic/global requirements. A quantitative bound with promising exponents is not yet a proved o(B³) theorem. No prime/ray/order/Anchor/rank claim. Structural/regression checks are not Lean validation.
