# Exact pointed thin-row barrier (original 318/326)

Source-only. The exact E=16 and affine comparison archives
6e78f72c… and 89a92a1f… are unchanged. This does not implement
the published prime majorant, dense model, concatenation, or PET
theorems. It does isolate their one remaining nonlinear use,
and closes finite signed reindexing/terminal bookkeeping
independently of any analytic assumption.

## One actual test per distinguished prime, not a universal nilsequence

Fix s, H (genuine selector, fixed field, tau and original q_step²-folded
distinct shifts), one already common sufficiently slow Y(N), and an
actual allowed row r at y=Y(N), physical N. Write n=r.n,
M0=r.M, m in [1,M0], x in Z/nZ represented by 1..n. In particular
M0=floor(floor(tau sqrt N)/W)−1 is the same OLD thin step width,
not the fine PET width. Let P_i(m)=shift r i m; use the old
cycle representatives for every f_i(x), μ_i(x). Set g_j=f_j−μ_j
and D_i(x)=1_{ceil(5n/8)≤x≤floor(3n/4)} (independent of i).
The right side of the exact original bound for the jth prefix is
n·M0·eps, without generator counts or a quotient/microbox factor.

Translate x to y'=x+P_j(m) in Z/nZ separately for each m. Define
the concrete, unnormalized dual test
  U_j(y')=Σ_{m=1}^{M0} D_i(y'−P_j(m))
          Π_{i<j} f_i(y'+P_i(m)−P_j(m))
          Π_{i>j} μ_i(y'+P_i(m)−P_j(m)).
The exact old mixed prefix is
  C_j=Σ_{y'∈Z/nZ} g_j(y') U_j(y').
No square is opened into independent v values; the same old m
drives all P_i(m). The dummy moves by −P_j; dropping that movement
gives a different test. This is an unnormalized identity even if
M0=0, q_step is negative, W even, or cyclic wraps repeat. The actual
analytic statement on occupied rows has n,M0>0.

A sufficient external assertion for the already written
MixedBudget consumer is, for each actual j<k and every allowed
row on this common schedule, |C_j|≤eps·n·M0, contingent on the
independently established literal LinearBudget at its prescribed
tolerance. No correlations against arbitrary nilsequences, all
2^k choices of cofactors, every thin box size, arbitrary q_step,
or varying selector field are required. Only one fixed prefix per
j is used. To cover signs use the published one-sided von Neumann
estimate on both ±g_j if desired.

For the LOWER-oriented endpoint a strictly weaker sufficient
assertion is Σ_{j<k} C_j≥−k·eps·n·M0 per row; no inverse bound.
Exactly
  mass(Π f)−mass(Π μ)=Σ_j C_j.
The finite clean geometry converts this to the identical signed
defect of r.phiRatio^k·rowRaw minus the actual periodic sum of
the means, without smoothing the dummy. Therefore it even suffices
to control the total signed defect over the original occupied rows
by −α^k S_s N T_phys/200; the periodic allowance uses its distinct
1/200 budget. This is a sufficient target, not a uniformly stronger
estimate. Only the per-row signed physical transfer is staged
here; the old full lower ledger already consumes the stronger
absolute row budgets. No code claims a new final theorem with
only aggregated signed errors.

## Exact narrow local-box/PET input and standard literature application

Use the published Tao–Ziegler, *Polynomial patterns in the primes*,
https://doi.org/10.1017/fmp.2017.3 (Theorems 9, 11, 13,
Proposition 4, Corollary 3). Its arXiv version
https://arxiv.org/pdf/1603.07817 Thm.4.1/equation (4.1)
gives the unambiguous fine box formatting in the scanned (57).
No general nilsequence estimate on short intervals is needed:
the bounded model is the way the theorem avoids that issue.

Geometry and the majorant: add exactly one bounded dummy R_0=0,
b_0=1. P_i(m)=d_i Wm²+2d_i c m+(b+d_ic²−b_i)/W. Each d_i is
nonzero and pairwise distinct, so every difference from the
distinguished P_j (including dummy−P_j) has degree exactly 2.
Use d=d0=2, r=1, D=k+1, prime factor ≤ the ordinary normalized
prime-only Λ'_{b_i,W} with its actual cutoff n^rho; μ_i∈[0,1].
Every retained b_i is a unit of the **squarefree** W, not a
modified repeated-prime wheel. Coefficients O_c(W) fit A=W^(1/rho)
for large Y. The dummy is bounded, its discontinuities immaterial.

The small nonlinear target local norm is only on PET-selected
tuples of affine integer forms L_l(h) (h in [M], tops determined
by actual P_i). Write
  L_P(g) = E_{h∈[M]} ||g||_{square^D'_{L_1(h)[-M,M],…,L_D'(h)[-M,M]}}
where M=M0/A, D'=O_k(1), coefficient magnitude ≤O(A^C) with fixed
C. Multisets include all original repetitions. Thm.13 controls
each signed C_j/(n M0) by K L_P(g_j)^c+o(1). For the lower only,
apply that theorem to −g_j; the real local box norm is sign
invariant, so this is a literal single family of tests per j.
The bound is on the actual row including its zero-shift dummy,
not on a square thin box with untwisted cofactors.

An explicit proof from the named results:
1. Choose B0>C+8 fixed and A*=A^B0, rho*=rho/B0 with the SAME
   W,n,M. Use Propos.4 + Cor.3 at A*, d=d0=2 for this
   chosen PET tuple to get one bounded model f'_j of f_j.
   It supplies simultaneously L_P(f_j−f'_j)=o(1) and
   ||f_j−f'_j||_{U^a_{q[J]}}=o(1) for each prescribed q,
   since a can be chosen large enough for the fixed PET orders.
   Cor.3 is used for arbitrary 0≤f_j≤Λ', not the special claim
   f'=1 for ordinary primes. The A* majorant threshold is smaller
   than the genuine n^rho threshold, preserving pointwise
   domination. The finite row/order constants are uniform
   within the fixed family as in the published theorem.
2. The actual linear cube FT/registered donor is on g_j alone,
   with original q≤(A*)^a and J=floor((A*)^(−2a)M²).
   It plus the global model comparison gives the small global
   U^a for f'_j−μ_j after rescaling by an absolute model
   bound B*=1+bound(f'_j). This holds at the SAME q,J and
   uniform selected j; never replace that by a bound at q=1.
   Theorem 9 gives small L_P((f'_j−μ_j)/B*), with D' and
   all actual resulting L_j fitting the chosen order/coefficients.
3. Add the two local norms (the multiset box Cauchy–Schwarz
   triangle inequality) and apply the signed Thm.13 estimate.
   Equivalently compare f_j−f'_j and f'_j−μ_j against the
   same explicit U_j using two PET estimates and the native
   split_at_model. In the latter route use the geometrically
   selected local PET shapes, not a model chosen from only some
   convenient unrelated tests. The single-family triangle route
   avoids any need to match two PET test selections.

All thresholds in this proof live on the ONE common Y(N); no
fixed-y arbitrarily-small nonlinear error is assumed. For the
normalizer/scales, at fixed tau>0 and large y one has M0∼tau sqrt(n/W),
n A^(−2B0 a−7)≲J and qJ≤n; M beats both fixed-y logarithmic
bounds; fix all exponents before choosing Y, with J bounded
below by a positive y-dependent multiple of n for the separate
fixed-y FT estimate. The divided width M in (57) is not M0
or M/A*; A* enlarges the coefficients/long global cube window,
while the fine physical M is unchanged. Use y(N) sufficiently
slow for TZ at rho and rho*, the affine threshold, physical
floors and CRT boundary. ε may depend on the already fixed S_s
and occupied-row bound; no uniformity in the fields or fixed-y
pointed continuation is needed.

## Why elementary cleaning or the linear marginal cannot suffice

A finite countercontrol isolates what is NOT asserted. With W=2,
b_i=1, n a multiple of 128, take the dyadic support S={y:2y+1=17
mod32}, one m and P_j=2 (for d=1,b=1,c=0). Let D be the actual
shifted dummy. The bounded artificial center
  g = 1_S (1_D−|D∩S|/|S|)
has zero mean in the supported class and is zero off the exact
dyadic support; matching a periodic conditional mean is exact.
Its actual normalized pointed correlation is
  |D∩S|/n · (1−|D∩S|/|S|)>0
bounded away from zero on this family. Therefore marginal
Chebotarev/CRT distribution by itself is insufficient, even with
the correct support. This does NOT claim a counterexample to
the high-order actual LinearBudget plus ordinary majorant and TZ;
it is not a model of weights of genuine primes.

## Source boundaries and regression

- ActualPointedCyclicPairing318: Mathlib-only exact integer cyclic
  translations at signed shift and finite pair/single-sequence
  reindex. No custom dependencies (1/0).
- ActualRayPointedAnchor318: literal old r.f, r.mean, r.dummy,
  old r.shift on Fin r.M, exact anchored comparison, fixed
  model split, old telescope reuse, and strongest useful signed
  row identity. Two files plus exact old telescope 32def3a5…
  (3/0 standalone for this algebra bundle).
- ActualRayPointedTransfer318: actual common-diagonal anchor
  adapter. The two historical forms eps*n*M0 and eps*(n*M0)
  are related only by explicit associativity; no changed scale.
  Uses frozen E=16 interface. No new outside consequence.
- ActualPointedPhysicalRow318: existing no-wrap/truncation
  physical cleaning produces exact signed log difference, then
  only the old finite-CRT strip is charged for a lower estimate.
  Direct deps old conditional lower and two anchor modules.
- Integer control tests 280 varied rows, 58,380 sites, 2,022 exact
  identities including 23 negative comparisons and separate
  marginal insufficiency. These do not use primes or prove
  any analytic statement. No build, push or dispatch.
