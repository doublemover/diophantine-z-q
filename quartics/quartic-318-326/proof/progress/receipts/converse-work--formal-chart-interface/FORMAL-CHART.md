# Actual nonarchimedean formal-chart norms

This generic packet works over any field F with an actual absolute value w:F→R and the nonarchimedean inequality. It assumes only w(D)≤1. No completeness, formal series, Hensel lifting, residue characteristic, minimality or prime classification is assumed.

## Checked statements

`affine_to_small_chart` starts from y²=x³−Dx and w(x)>1. Dominance gives w(y)²=w(x)³, then y≠0, w(y)>1, and the actual coordinates z=−x/y,t=−1/y both have absolute value below one. Their exact equation t=z³−Dzt² is proved algebraically.

`small_chart_to_pole` starts from nonzero small z,t with that equation. The factor 1+Dzt has absolute value one, so w(t)=w(z)³ and w(z/t)>1. Thus these are the actual x-pole charts, not an abstract neighborhood assumption.

`chord_small` defines exactly

- λ=(z1²+z1z2+z2²−Dt2²)/(1+Dz1(t1+t2));
- ν=t1−λz1;
- q=1−Dλ²;
- z3=2Dλν/q−z1−z2;
- t3=λz3+ν.

If all four input chart coordinates are small, the two displayed denominators have absolute value one, and λ,ν,z3,t3 are small. The bound w(2)≤1 follows from nonarchimedeanity, so the proof includes primes above two. Equal input charts specialize this same formula to the tangent case.

Six elementary norm helpers and these three results are kernel-checked.

`FormalChartDouble.lean` adds five results over a characteristic-zero field: the actual short-curve ordinate equation, actual doubling square formula, its nonarchimedean pole inequality, and affine/point-level actual group doubling closure. `point_double_pole` proves w(xRep(Q+Q)(0))>1 whenever w(xRep(Q)(0))>1. The identity and zero-ordinate branches are discharged, and the conclusion is stronger than a possible-infinity disjunction. This module uses the actual `ReciprocalDouble318.E D`; the constant-two absolute value may be less than one, so residue characteristic two remains included.

All fourteen results are kernel-checked. All axiom roots are propext, Classical.choice and Quot.sound. `verify.sh` reproduces the check; `receipt.json` binds the exact files.

## Scope boundary

This package proves the norms, the chart equation and its pole equivalence. The exact secant chord/Vieta identification with actual elliptic group addition and the resulting full subgroup assembly belong to `height-work/FormalChordAlgebra318.lean` and the height worker's continuation. No actual group law is silently assumed by the norm packet. No live height or repository source was edited.
