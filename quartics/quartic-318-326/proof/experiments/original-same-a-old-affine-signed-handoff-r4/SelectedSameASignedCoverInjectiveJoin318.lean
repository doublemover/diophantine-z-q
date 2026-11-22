module

public import SelectedSameASignedLiftCocycle318
public import SelectedSameALocalImageLift318
public import SelectedSameASignedOpenInjectiveImage318

/-!
# The signed coefficient of the image lifts on the actual old cover

The old local lifts are retained as actual input. This theorem produces
their image-lift equations and identifies the existing target signed
coefficient, without assuming a target lift family or its coefficient.
-/

public section

open CategoryTheory Opposite TopologicalSpace

namespace SelectedSameASignedCoverInjectiveJoin318

universe u

open SelectedSameALiteralInjectiveRow318
open SelectedSameASignedLiftCocycle318

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable {S : ShortComplex (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})}
variable {L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- On every original pairwise intersection the actual right-minus-left
coefficient of the image lifts is the old coefficient evaluated by
the very left map in the contracted boundary. -/
theorem factor_cover_coeff (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L)
    {ι : Type u} (U : ι → Opens X)
    (z : S.X₃.obj.obj (op (⊤ : Opens X)))
    (t : ∀ i, S.X₂.obj.obj (op (U i)))
    (ht : ∀ i, S.g.hom.app (op (U i)) (t i) = res X S.X₃ le_top z) :
    let T := target X L
    let G := factor X hOld lambdaA
    let z' := G.τ₃.hom.app (op (⊤ : Opens X)) z
    let t' := fun i => G.τ₂.hom.app (op (U i)) (t i)
    ∃ hImage : ∀ i, T.g.hom.app (op (U i)) (t' i) = res X T.X₃ le_top z',
      ∀ i j, coeff X T (target_shortExact X L) U z' t' hImage i j =
        lambdaA.hom.app (op (U i ⊓ U j)) (coeff X S hOld U z t ht i j) := by
  let T := target X L
  let G := factor X hOld lambdaA
  let z' := G.τ₃.hom.app (op (⊤ : Opens X)) z
  let t' := fun i => G.τ₂.hom.app (op (U i)) (t i)
  have hT : T.ShortExact := target_shortExact X L
  have hImage (i : ι) : T.g.hom.app (op (U i)) (t' i) = res X T.X₃ le_top z' :=
    SelectedSameALocalImageLift318.factor_local_lift X hOld lambdaA (U i) z (t i) (ht i)
  refine ⟨hImage, ?_⟩
  intro i j
  let W := U i ⊓ U j
  let li : W ≤ U i := inf_le_left
  let rj : W ≤ U j := inf_le_right
  let b := coeff X S hOld U z t ht i j
  let FW := T.f.hom.app (op W)
  let SW := G.τ₂.hom.app (op W)
  have hSource : S.f.hom.app (op W) b =
      res X S.X₂ rj (t j) - res X S.X₂ li (t i) :=
    coeff_beta X S hOld U z t ht i j
  have hTransport :
      FW (lambdaA.hom.app (op W) b) =
        SW (res X S.X₂ rj (t j)) - SW (res X S.X₂ li (t i)) :=
    SelectedSameASignedOpenInjectiveImage318.factor_right_minus_left
      X hOld lambdaA W b (res X S.X₂ li (t i)) (res X S.X₂ rj (t j)) hSource
  have hr : res X T.X₂ rj (t' j) = SW (res X S.X₂ rj (t j)) :=
    (res_natural X G.τ₂ rj (t j)).symm
  have hl : res X T.X₂ li (t' i) = SW (res X S.X₂ li (t i)) :=
    (res_natural X G.τ₂ li (t i)).symm
  change coeff X T hT U z' t' hImage i j = lambdaA.hom.app (op W) b
  apply SelectedSameAActualLiftDifference318.local_inclusion_injective X T hT W
  change FW (coeff X T hT U z' t' hImage i j) = FW (lambdaA.hom.app (op W) b)
  calc
    _ = res X T.X₂ rj (t' j) - res X T.X₂ li (t' i) :=
      coeff_beta X T hT U z' t' hImage i j
    _ = SW (res X S.X₂ rj (t j)) - SW (res X S.X₂ li (t i)) :=
      congrArg₂ (fun x y : T.X₂.obj.obj (op W) => x - y) hr hl
    _ = FW (lambdaA.hom.app (op W) b) := hTransport.symm

end SelectedSameASignedCoverInjectiveJoin318
