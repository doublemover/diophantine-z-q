# Actual affine elliptic base change

Two strict-kernel-checked modules identify the genuine tensor base change and Scheme pullback with the actual changed-coefficient model.

`AffineBaseChange318` constructs the coefficient map from the exact quotient universal property, the forward tensor-product map, and the reverse map from actual equation solutions in the tensor product. It proves both inverse algebra-homomorphism identities, obtaining

S ⊗[R] (R[x,y]/(y²−x³−Ax−B)) ≃ₐ[S] S[x,y]/(y²−x³−A_S x−B_S).

The exact x/y images and a literal OpenJModel specialization are included. No injectivity, flatness, discriminant-unit or coefficient-field premise is required for this identity.

`AffineSchemeBaseChange318` composes that algebra equivalence with Mathlib's actual affine-pullback/tensor-product isomorphism. Its `schemeIso` is an isomorphism of genuine Schemes, and both forward and inverse maps commute with the actual base projection. `literalFiberIso` specializes to every algebra over the literal OpenJ base.

This removes the former tensor/fiber model-identification boundary for the affine chart. Proper/projective completion, gluing base change for the completed curve, relative group and torsion schemes, and identification with a specified arithmetic modular family remain separate. Those are not inferred from the affine isomorphism.

Replay: `bash run.sh`, with `debug.skipKernelTC=false`. Audit exhaustively checks every declaration of both modules for standard axioms only.
