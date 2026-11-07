# Actual integral affine j-model and original open cover

This packet constructs a genuine Mathlib Scheme, not just a height or a ring-normality premise. If B is an actual finite algebra over R[1/d], it takes A to be the actual integral closure of R in B and constructs Spec A over Spec R.

Every b in B is integral over R[1/d]. The proved denominator-clearing theorem supplies n with d^n*b integral over R. This proves that the actual inclusion A→B is a localization at the actual image of d. Therefore Spec B is an actual open subscheme of Spec A, with exactly the denominator basic open as its image. The packet constructs the actual scheme isomorphism to that open and proves compatibility with the ambient model.

The source specialization uses R=Z[j], d=6N*j*(j−1728), and the existing actual OpenJModel318.Base N. It constructs the actual model, the original finite-etale cover when B is genuinely finite etale, and the commuting open-cover diagram over the j-line.

## Scope

The structure morphism of the constructed model is integral. The proof deliberately does not infer finiteness from integrality. In general an integral closure inside a localized algebra with nilpotents need not be finite. This packet does not construct the source primitive-torsion algebra B or its equivariant splitting, and it does not construct a projective/proper completion or the final Shimura/modular stack. Those actual source-object bindings remain separate. No final height theorem or geometric-realization existence is asserted.

## Replay

Run `bash build.sh`. Both source modules are strictly kernel-rebuilt and every declaration recursively audited against only propext, Classical.choice and Quot.sound. No repository, Git or Mathlib source is modified.
