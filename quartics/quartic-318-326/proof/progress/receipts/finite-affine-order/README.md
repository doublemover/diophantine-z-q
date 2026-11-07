# Actual finite affine order and finite open-cover model

For a genuine finite algebra B over R[1/d], this packet constructs an actual finite R-subalgebra A of B such that B is the actual localization A[1/d]. No finiteness of an integral closure is assumed.

The proof first derives that B is finite type over R, since localization away one element is finitely presented and B is finite over it. It chooses finite algebra generators and clears a power of d in each generator to an element integral over R. Their actual adjoin is finite as an R-module. The set of elements whose denominator can be cleared into that subalgebra is proved to be an R-subalgebra; it contains all original generators and is therefore all of B. This proves the actual localization property.

The chosen suborder then supplies a genuine Mathlib Scheme Spec A, an actual finite structure morphism to Spec R, hence proper over that affine base, and an actual open immersion and isomorphism identifying Spec B with precisely D(d). The ambient diagram commutes. The final source specialization uses the literal base OpenJModel318.Base N and denominator 6N*j*(j−1728), giving an actual finite model over the integral affine j-line.

## Exact boundary

The finite suborder need not be normal. This is not a finiteness assertion about the full integral closure. Properness is relative to Spec R; the packet does not compactify the affine j-line or construct the projective modular curve. It still requires the actual source finite open algebra B. It does not construct primitive torsion, the global Shimura stack, controlled fiber fields, or final geometric-realization existence.

The earlier affine-integral-model packet constructs the full integral-closure model and its original open but does not claim that model finite. These two constructions have different stated strengths; neither is silently substituted for the other.

## Replay

Run `bash build.sh`. Both modules are strictly kernel-rebuilt and all declarations recursively checked against only propext, Classical.choice and Quot.sound. No repository/Git/Mathlib source edits.
