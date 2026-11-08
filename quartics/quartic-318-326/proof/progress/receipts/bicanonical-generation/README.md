# Local generation by the global bicanonical pair

This two-source continuation proves that the actual global q0 and q1 from the
frozen global-bicanonical-sections packet generate the actual intrinsic
cotangent tensor-square sheaf locally everywhere on the complete contact
normalization, for every chosen rational unit twist.

## Exact endpoint

`ContactBicanonicalGenerators318.generate_on_neighborhood` says that for every
actual source point x there is an open V containing x such that either q0 or
q1 freely generates on every subopen W of V. Precisely, multiplication by its
restriction is a bijection from O(W) to the tensor-square module sections on W.
This is a local sheaf-generation/base-point-free statement, not merely a
surjectivity assertion on the sections of one neighborhood.

The stronger chart-specific endpoints are:

- `global_branch_generator`: global q0 freely generates on every subopen of
  each of the four actual finite branch charts.
- `global_infinity_generator`: global q1 freely generates on every subopen
  of the entire actual infinity chart.

`generate_at_every_point` records the corresponding neighborhood-section
bijection as a simpler corollary-like endpoint. The universal-subopen theorem
is the controlling local-generation statement.

## Proof and coefficients

A generic intrinsic tensor frame is constructed using the actual cotangent
chart comparison, tensor restriction, tensor congruence and the unit tensor
multiplication map. It sends the tensor square of the normalized universal
coordinate derivative to scalar one. Restricting the global structure sheaf
then supplies an actual local frame, so the generator property holds on every
ambient subopen.

Multiplying that generator by a regular unit coefficient preserves this
property. Unit status is transported by the exact Gamma-Spec identification,
actual chart appIso and actual restriction map. The finite q0 coefficients
are units on their full branch charts; the infinity q1 coefficient is a unit
on its full chart. Finally, the already checked exact restrictions of the
actual global sections and the five-chart cover give the stated conclusion.

## Scope

The direct universal-coordinate global construction is unchanged. No old
inverse-frame section name is silently substituted. This packet does not yet
construct the projective morphism associated to the pair, prove linear
independence, compute its degree, identify a PEL source or compare a
Kodaira-Spencer map. The arbitrary twist units have not been selected from a
Shimura model.

## Validation

Both sources receive a fresh bounded strict replay. The joined audit includes
the complete 48-module global-section dependency join and these two modules,
checking all declarations against only propext, Classical.choice and Quot.sound.
Exact results, source hashes, application obligations and predecessor bindings
are recorded in receipt.json and APPLICATION.json. No fresh whole-repository
rebuild or independent-review verdict is implied by this producer receipt.
