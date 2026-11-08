# Exact five-contact producer ledger

## What this packet does, and what remains

`FiveContactProducer318.five_contact_of_realization` is kernel-checked. It derives the **exact** `ContactHeight318.FiveContact49Height` predicate from `GeometricRealization`. The latter is an explicit existence statement for one of two concrete producer records at each primitive input point. Neither record contains the desired final contact bound. The CM record has actual discriminant/prime-support/eta-period/isogeny inputs; the non-CM record has actual complex cusp functions and area energies, a finite intersection matrix and section data, the three named Arakelov identifications, and image/isogeny/contact-metric inputs. The actual support parameter is fixed to the literal bad-prime product times the actual odd-contact radical.

**`GeometricRealization` is not asserted or axiomatized.** This is the remaining formal realization obligation. It is substantially more explicit than an unexplained five-contact height axiom, but it still requires constructing the actual algebraic geometry and identifying its invariants with the records. Counting the record projections as new geometric theorems would be misleading. This module has seven public theorems; its exhaustive audit counts87 declarations, most of them generated structure projections/recursors.

The coordinated reports below give the mathematical construction and named classical theorem applications for these data. They do not turn schemes, abelian varieties, Galois representations, Hodge bundles or arithmetic intersections into Lean objects merely by describing them. Thus the final literal source theorem remains conditional in Lean until this realization input is discharged. No counterexample to the claimed classical application has been established by the reported checks.

## 1. Literal input and the two different rational coordinates

Given coprime integers u,v with all five literal forms nonzero, put

s=u/v,   t=32s,   R=B_bad*M(u,v).

The five forms are v,u,u−v,u−2401v,32u+343v. `source_contact_avoidance` proves v is nonzero and s avoids0,1,2401,−343/32. The fifth branch contact is infinity. `pointHeight_eq_contact_height` and `scaled_metric_height` prove the exact Mathlib identity between source projective height and the height of t/32. No unknown height normalization or coordinate-loss constant enters this identification. `support_ge_one` proves R>=1 from the actual finite prime product.

The input contact s can be negative. Later the modular Jacobian argument selects an **unrelated auxiliary** rational a_i=1/(2^128+i) in(0,1). Positivity is needed for that auxiliary point's three-contact finite bound, not for the original input. These symbols must not be conflated.

## 2. Actual contact curve and controlled fiber surface

`fiber-field-bridge/FIBER-PRODUCER.md` reconstructs the discriminant210 quaternionic Shimura quotient from the original Gonzalez–Rotger models. The four genus-one quotients, tame stabilizers, genus5 Riemann–Hurwitz and inertia relation give precisely five rational branch points of order2. `contact-coordinate-bridge/ContactCoordinates318.lean` proves that their four actual labeled quartic invariants force the unique tuple infinity,0,1,2401,−343/32. The theorem proves six-cross-ratio exhaustiveness internally and eliminates all36 pairs; the older Python calculation is no longer the strongest arithmetic check.

The same report constructs the **whole** principal-level-three canonical model action, not one chosen component. Central ideles and the ramified local order give effective level kernel36 and normalizer group576. The complete unbranched fiber is a regular constant-group torsor. Its normal splitting field L has Galois action commuting with this torsor. `FiberCentralizer318.galois_torsor_degree_576` then proves the actual finite-Galois degree divides576, rather than using a factorial bound.

The integral tame model gives L unramified outside210 and positive odd contacts, and gives the actual fiber surface A good reduction over L at **every** prime outside210, including primes where L itself is ramified. The latter stronger assertion follows from properness of the fine model and its universal abelian scheme. Full three-torsion markings give same-field descent of all geometric Hom maps: each difference kills A[3], hence lies in3Hom; finite individual Galois orbits then imply trivial action by the checked integral-lattice/congruence packets. The abelian Hom lattice, quotient-by[3] and descent are actual classical application facts, not supplied by the matrix theorem alone.

The exact primitive contact support agrees with R, as checked in `conductor-support/CONDUCTOR-REVIEW.md`. It is not inferred solely from branch-determinant numerology.

## 3. Common geometric metric-to-contact comparison

Use the maximal regular, proper, semistable quaternionic stack with its universal abelian surface. The metric coordinate is t=32s, whose finite contacts are0,32,76832,−343. `isogeny-height-transfer/METRIC-PRODUCER.md` proves the smooth branch/infinity extensions, actual curvature calculation, compact maximum-principle comparison and exact Petersson factor4. The literal distance and valuation arithmetic is kernel-checked in `five-contact-metric`.

The two bicanonical sections q0=(dt)^2/product(t−a_i), q1=t*q0 have no common generic zero. Multiplying by J^2 makes them integral at every vertical generic point; semistable regularity and codimension-one extension give global sections. Yuan's actual maximal-stack isometry has image210*omega^2. Its exact normalization and the integral-section evaluation give

h(s) <= 2h_original(A)+120,

and the same inequality with the larger shifted height. The sign of log210 is positive; the original-to-shifted surface correction is+log(pi). The finite constants are bounded in `MetricCancellation318`. The current actual NumberField section-height producer and exact stack/universal-surface pullback ledgers refine this last application; their final artifacts are listed in the integration supplement when frozen.

Pulling back to evaluate the integral stack section may require an auxiliary finite extension. Stable normalized heights are unchanged. This auxiliary evaluation field is **not** the controlled field in the isogeny theorem, so it must not be substituted into its degree bound.

## 4. CM branch: original surface height, not contact854R

If A is CM, its quaternion division action forces A geometrically isogenous to E^2 for a CM elliptic curve. Same-field endomorphism descent makes the idempotents, factors, isogenies and maximal-order quotient defined over L. The CM field embeds into L through its action on the elliptic tangent line. Its fundamental discriminant therefore has radical supported on that of L and magnitude at most4R.

`cm-height-producer/CM-PRODUCER.md` reconstructs these geometric inputs and checks the original Silverman normalization and GR isogeny theorem. Its Lean modules use an actual fundamental discriminant, actual finite radical, actual convergent Mathlib Dedekind eta product, reduced periods, finite averaging and the exact squared Xi degree expression to prove **h_original(A)<854R**. The averaging extension degree q is separate from the original field degree d<=576.

`cm-contact-assembly/CMContactAssembly318.lean` consumes that producer directly and composes with the factor2/+120 geometric comparison, or the exact+log(pi) shifted comparison, to reach the required contact cap. Neither a surface854R premise nor a contact854R premise is supplied there.

Correction to a frozen historical description: `IsogenyHeightTransfer318.contact_height_CM` and its old README describe a generic conditional lemma assuming contact height<=854R. That lemma is valid, but the source does not supply its premise. The actual CM application is the corrected surface-to-contact composition just described. Frozen files were not silently edited.

## 5. Non-CM branch: actual modular source and degree

`conductor-support/CONDUCTOR-REVIEW.md` checks the scalar sign lift, controlled normal field L', Pan's prime5 theorem, the3/5 compatible-prime switch, full conductor compatibility and wild/tame bounds. It supplies

[L':Q]<=2304R,   N<=210^300 R^2,   rad(N)|R.

The actual nebentypus square relation on G_L' gives a kernel index at most4608R. The checked group/root-count proof distinguishes image cardinality from character exponent. `EulerIndex318` proves the finite Euler-product bound.

`modular-factor-producer/MODULAR-FACTOR-PRODUCER.md` constructs the actual point-level X_H/Q for H=ker(epsilon), with all coefficient conjugates in its factor. It explicitly reconciles the point-level and mu_N models by the rational dual-isogeny/Fricke transport; no Q-rational cusp on the wrong model or cyclotomic enlargement is assumed. Jacobian norm identities, coefficient-Hom descent and Faltings produce a nonzero A->J_H over the same L', with image dimension2. Thus g>=2. The central−I convention gives the exact degree

d=N*[units:H]*product(1+1/p) < 2^14*210^300*R^(97/32),

without factor2 or coefficient-field degree, and g<=d.

## 6. Actual modular integral model, finite divisor and local analysis

`modular-integral-producer` constructs the literal elliptic Weierstrass model over the localization Z[j,1/(6N*j*(j−1728))], with an actual discriminant-unit/IsElliptic/j proof. The mathematical finite-etale torsion/H quotient, including primes dividing|H|, identifies the exact point-model open cover. Reconstructing its normalization after every number-ring extension proves vertical branch support p|6N. It does not assume that arbitrary global normalization commutes with ramified base change.

The whole-fiber counting argument selects the auxiliary a_i so that every conjugate of b is non-Weierstrass. The actual cusp packet proves embedded charts, radius>=exp(−21)/N and the differential-log bound. The actual Wronskian packet proves the factorial-normalized derivative determinant bound from genuine holomorphic disc integrals, using Cauchy/variance and actual two-dimensional polar integration. The chart-energy transport packet further connects pullback coefficients to the global norm-one energy; global differential/measure interpretation remains the geometric identification.

`finite-divisor-producer-review` freshly verifies Javan4.3.2's minimal regular semistable resolution and crucial p<=d branch condition. At nonexceptional generic points the actual different bounds give K<=f*D_bound. The negative-definite exceptional argument extends this inequality without assuming a Cartier ramification divisor on the singular normalization. The chosen section maps with degree1 to the base section, so its finite bound has **no d factor**. The auxiliary0<a_i<1 condition is explicit; the assertion would be false for an arbitrary signed rational input. The matrix and exact horizontal/floor-log arithmetic are kernel-checked. The new actual local-different packet refines the remaining local coefficient producer.

## 7. Exact Arakelov and final quantitative join

`converse-work/cusp-jacobian-glue` binds actual embedding-indexed cusp functions, energies, finite matrix/section data and the named minimal-model/Faltings-Wronskian/normalization identities. The two metric terms use the **same** local coordinate at each embedding and cancel with k=g(g+1)/2. The field-average denominator is the number-field degree; complex embeddings already account for the factor2 convention. The original-to-shifted Jacobian correction is+g*log(sqrt(pi)). The independently replayed `javan-sign-review` checks these exact signs and hypotheses.

The resulting kernel theorem derives

h_shifted(J_H)<=2^11*d^2*log(6dN)^2.

The checked actual-log growth uses log(6dN)<2^13 R^(1/32), so 2*(97/32)+2*(1/32)=49/8. Actual image-height monotonicity and the dimension-linear lower bound give h(image)<2^66 C^2 R^(49/8). The dimension-two GR isogeny and half-log variation over the controlled field give h_shifted(A)<2^67 C^2 R^(49/8). The contact metric comparison gives exactly

pointHeight(u,v)<2^68*(210^300)^2*R^(49/8)+128.

`NonCMData.bound` consumes the checked non-CM theorem; `CMData.bound` consumes the checked CM theorem. `five_contact_of_realization` performs their disjunction and discharges the exact five-contact predicate, with all constants and support fixed rather than inferred from an older exponent24 estimate.

## 8. Exact remaining formal work

The code still does not construct the actual Shimura/modular schemes, universal abelian varieties, Hodge bundles, complex uniformizations, Galois representations or arithmetic intersection forms. The concrete fields of the records must be instantiated from those objects, using the named classical theorems above. In particular the formal fields `contact_metric`, the three Arakelov identifications, actual image/isogeny application, and CM period/product identifications are still producer inputs, even though their mathematical applications have been traced and independently reviewed.

The new finite and analytic packets remove specific inequalities and normalization ambiguities. They do not license deleting `GeometricRealization` or treating it as true by definition. An unconditional Lean proof would require the missing global AG/arithmetic realizations or an explicitly accepted external theorem interface; no `axiom`, `sorry`, or unchecked native computation is introduced here. This is the precise distinction between source-level proof validation and a completed kernel proof of the global theorem.
