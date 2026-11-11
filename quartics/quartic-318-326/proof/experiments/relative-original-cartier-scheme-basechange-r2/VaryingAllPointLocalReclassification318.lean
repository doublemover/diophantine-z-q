module
public import VaryingLocalFreeIdealGluing318
public section
noncomputable section
namespace VaryingAllPointLocalReclassification318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S)
/-- Reconstructing an arbitrary parameter point from its intrinsic full
ideal and its PROVED local free cover returns that exact point. This
right inverse holds on ALL points, not merely the global-free locus. -/
lemma classify_recover : VaryingLocalFreeIdealGluing318.point R A ι S
    (VaryingParameterPointIdeal318.ideal R A ι S x)
    (VaryingLocalFreeIdealCover318.ofPoint R A ι S x)=x := by
  symm
  apply VaryingLocalFreeIdealGluing318.unique
  intro i
  have h := congrArg Subtype.val (VaryingAllPointLocalFreeIdeals318.classify_local R A ι S x i)
  exact h.symm
end VaryingAllPointLocalReclassification318
