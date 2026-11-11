module
public import OriginalHOnePointedEquivalence318
public import AffineHOnePicardKernelHom318
public section
noncomputable section
namespace OriginalHOneKernelGroupEquivalence318
open AlgebraicGeometry CategoryTheory
open DualNumberScheme318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ base R)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hc : U ⊔ V = ⊤)
include hUV in
lemma bijective : Function.Bijective (AffineHOnePicardKernelHom318.kernelHom p U V hU hV hc) := by
  constructor
  · intro x y h
    change x.toAdd = y.toAdd
    apply (OriginalHOnePointedEquivalence318.equivalence p U V hU hV hUV hc).injective
    apply DualNumberPointedKernel318.forget_injective p
    exact congrArg Subtype.val h
  · intro c
    let c' : SplitReductionPointedKernel318.Kernel (reduction R p) := ⟨c.val,c.property⟩
    obtain ⟨x,hx⟩ := (OriginalHOnePointedEquivalence318.kernelEquivalence p U V hU hV hUV hc).surjective c'
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    exact Subtype.ext (congrArg Subtype.val hx)
/-- Tensor multiplication on the ORIGINAL restriction kernel corresponds to
addition in ORIGINAL H1. This upgrades the old kernel homomorphism itself. -/
@[expose] def equivalence : Multiplicative (SheafCohomologyRetraction318.structureH X 1) ≃*
    (LineClassPullbackHom318.pullback (reduction R p)).ker :=
  MulEquiv.ofBijective (AffineHOnePicardKernelHom318.kernelHom p U V hU hV hc)
    (bijective p U V hU hV hUV hc)
lemma apply_eq (z : Multiplicative (SheafCohomologyRetraction318.structureH X 1)) :
    equivalence p U V hU hV hUV hc z = AffineHOnePicardKernelHom318.kernelHom p U V hU hV hc z := rfl
end OriginalHOneKernelGroupEquivalence318
