# Independent review: actual invariant-base torsor construction

Accepted at the stated algebraic and affine-scheme scope. Exact copies of the two quotient-cover modules, one faithful-flat torsor module and two invariant-base binding modules were freshly strictly compiled. Their exhaustive audits passed38,30 and48 declarations respectively, for116 declarations in5 modules. Only propext, Classical.choice and Quot.sound occur. Source hashes were checked after replay.

The quotient inclusion is actually faithfully flat: finite étale gives flatness, and integrality plus its actual injective subalgebra inclusion gives surjectivity on prime spectra. The corresponding actual Spec map is surjective finite étale and a topological quotient map.

For a free action on the genuine splitting set, orbit representatives give an actual bijection G×(X/G)→X. This constructs an algebra equivalence over the actual invariant algebra, not just an equality of ranks. The split torsor isomorphism is explicitly identified on pure tensors as b⊗c ↦ (g ↦ b·ρ(g)c). Empty/trivial cases do not introduce a spurious nonempty-fiber premise; the separate finrank statement explicitly requires nontrivial coefficients and a nonempty set.

The faithful-flat descent module checks the canonical map itself under the actual double-tensor and finite-product base-change identifications. Faithful flatness then reflects its bijectivity. A supplied torsor-law or unnamed isomorphism of equal-rank modules is not used.

The final binding genuinely changes the splitting base from R to D=B^G. TensorTower318 defines the actual D⊗R S algebra structure on B⊗R S and derives its pushout equivalence. The formula on a pure tensor is checked. The two invariant and cover coordinate identifications are shown compatible with the actual inclusion. This constructs a regular splitting over D⊗R S. Its equivariance is proved on nested pure tensors, with the exact g*h convention appropriate to pullback automorphisms. Finally the D-faithfully-flat extension descends the canonical map. The resulting invariantTorsorEquiv has the exact formula b⊗c ↦ b·ρ(g)c.

Remaining inputs are the actual primitive-torsion cover and its genuine free equivariant splitting, and the identification with the source modular/sheaf quotient. These packets do not construct those source objects from finite group counts. No global refined geometric realization is asserted.

Run `bash build.sh`. Copied project sources and copied downstream dependencies are first on LEAN_PATH; frozen orbit-algebra/Mathlib oleans are reused. This is an independent project replay and bounded mathematical review, not a recompilation of all imported libraries or a proof of the remaining global geometry.
