module
public import VaryingLocalFreeIdealRecovery318
public import VaryingAllPointLocalReclassification318
public section
noncomputable section
namespace VaryingLocalFreeQuotientEquiv318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- Geometrically locally free full quotient ideals. The definition is
by actual affine coefficient charts and free extended quotients, not by
the range of a classifying map or an existential parameter point. -/
abbrev LocalIdeal := {I : Ideal (S ⊗[R] A) // Nonempty (VaryingLocalFreeIdealCover318.Data R A ι S I)}
@[expose] def classify (I : LocalIdeal R A ι S) : VaryingParameterPoint318.Point R A ι S :=
  VaryingLocalFreeIdealGluing318.point R A ι S I.val (Classical.choice I.property)
@[expose] def recover (x : VaryingParameterPoint318.Point R A ι S) : LocalIdeal R A ι S :=
  ⟨VaryingParameterPointIdeal318.ideal R A ι S x,⟨VaryingLocalFreeIdealCover318.ofPoint R A ι S x⟩⟩
lemma recover_classify (I : LocalIdeal R A ι S) : recover R A ι S (classify R A ι S I)=I := by
  apply Subtype.ext
  exact VaryingLocalFreeIdealRecovery318.ideal_classify R A ι S I.val (Classical.choice I.property)
lemma classify_recover (x : VaryingParameterPoint318.Point R A ι S) : classify R A ι S (recover R A ι S x)=x := by
  apply VaryingAllPointIdealSeparation318.ideal_injective R A ι S
  exact VaryingLocalFreeIdealRecovery318.ideal_classify R A ι S
    (VaryingParameterPointIdeal318.ideal R A ι S x) (Classical.choice (recover R A ι S x).property)
/-- Genuine two-sided classification on ALL actual parameter points,
now with locally free rather than globally free quotient ideals. -/
@[expose] def equivalence : LocalIdeal R A ι S ≃ VaryingParameterPoint318.Point R A ι S where
  toFun := classify R A ι S
  invFun := recover R A ι S
  left_inv := recover_classify R A ι S
  right_inv := classify_recover R A ι S
end VaryingLocalFreeQuotientEquiv318
