# Actual fine-level quotient covering and atlas

Strict-kernel PASS: 9 declarations in 2 modules, including 5 public theorems. The exhaustive recursive audit permits only propext, Classical.choice and Quot.sound.

The group is the actual image in GL2+(R) of Mathlib Gamma1(N), acting on the actual upper half-plane. Proper discontinuity is derived from the genuine integral modular-group action: the compact-intersection set injects into the corresponding finite set for SL2(Z). It is not supplied as an input. For N>=5 the independently proved fixed-point freeness is installed as the standard cancellative-action interface.

`GammaOneAtlas318.quotientMap` is the actual orbit projection onto the exact base quotient used by the Petersson differential-fiber construction. `quotient_covering` constructs its genuine quotient-covering property, `quotient_localHomeomorph` gives the actual local homeomorphisms, and `quotient_hausdorff` proves that the quotient is Hausdorff. The projection is actually surjective.

`chartedSpace` constructs a genuine Mathlib ChartedSpace with complex coordinates by pushing the ordinary open-embedding chart of the upper half-plane through the proved surjective local homeomorphism. `exists_chart` gives an actual open partial homeomorphism around every quotient point. Thus this packet supplies a topological atlas on an actual quotient object, not a structure with an assumed atlas field.

Boundary: complex/holomorphic transition maps and a registered complex-manifold structure are not proved here. Compactification and cusp charts, the specified arithmetic/PEL/modular-family identification, an arithmetic model and global section realization remain separate. The freeness conclusion applies to Gamma1(N), N>=5, not arbitrary intermediate or diamond quotients.

Replay: run `bash gamma-one-quotient-atlas/build-all.sh` from the parent directory. All modules are rebuilt with `-Ddebug.skipKernelTC=false` before the audit. Lean 4.35.0 and pinned Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 remain unchanged. Eight official cache files supporting proper modular action and quotient charts were fetched without source modification. No Git/repository files were changed.
