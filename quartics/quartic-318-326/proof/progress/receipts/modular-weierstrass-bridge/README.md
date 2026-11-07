# Actual normalized Weierstrass and modular j binding

Strict kernel replay and full recursive audit pass: two modules, 17 declarations, standard axioms only.

`NormalizedWeierstrass318.model c4 c6` is an actual complex Weierstrass curve with a1=a2=a3=0, a4=-c4/48, a6=-c6/864. Its actual c4 and c6 invariants equal the input values, and its discriminant is (c4^3-c6^2)/1728. Its actual elliptic j has the corresponding formula.

`ModularWeierstrass318.curve tau` specializes to the genuine normalized weight-four and weight-six Eisenstein modular forms. The module proves:

- actual curve c4=E4(tau), c6=E6(tau);
- actual curve discriminant equals the genuine modular discriminant eta(tau)^24, by Mathlib's proved `discriminant_eq_E₄_cube_sub_E₆_sq`;
- actual discriminant is nonzero, hence the model is unconditionally an elliptic Weierstrass curve;
- `curve_j`: its actual `WeierstrassCurve.j` equals `ActualQJ318.jInvariant tau`;
- `G_qParam_curve_j`: the actual analytic G at q(tau) equals q(tau) times this actual algebraic j.

No discriminant identity, j equality, coefficient relation, or nonvanishing assumption is supplied as a premise.

## Exact remaining interpretation

This constructs the genuine normalized algebraic model from the genuine Eisenstein values. It does not prove that a specified modular-curve fiber or a specified complex torus is isomorphic to that model. Mathlib has actual `PeriodPair.weierstrassP`, its derivative, lattice invariants g2/g3, and the Weierstrass differential equation. Its `PeriodPair.G` source still explicitly marks the connection to the modular-form library as a TODO; no existing uniformization/model-identification theorem was located. That lattice/moduli interpretation is therefore retained, not silently inferred from the name of the curve. The packet still removes the actual invariant/discriminant/j/qj algebra from that remaining identification.

## Replay

Run `bash run.sh`. It strictly rebuilds both modules and audits every generated/private declaration. Dependencies include the actual-qj producer, E4 producer and standard Mathlib LevelOne/GradedRing. Four missing official Mathlib cache files for GradedRing were obtained from the official cache; no source or repository was modified. Dependency source hashes are recorded in the receipt.
