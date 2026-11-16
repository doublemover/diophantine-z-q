module
public import ActualTwoDescentSelmerRankAlternative318
public section
noncomputable section
namespace ActualTwoDescentContinuousHOneEmbedding318
set_option maxHeartbeats 16000000

open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentFieldActualGaloisCohomology318
open groupCohomology
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Gal" => Field.absoluteGaloisGroup F

/-- Every actual continuous E[2] cocycle is represented in Mathlib's ACTUAL H1. -/
def continuousGroupCocycle (n : F) (χ : continuousCocycles n) : cocycles₁ (actualTwoTorsionRep n) :=
  ⟨fun σ => ((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd,by
    apply (mem_cocycles₁_iff _).mpr
    intro σ τ
    rw [Representation.isTrivial_apply]
    have h := congrArg Multiplicative.toAdd ((χ : Gal →* Multiplicative (closedTwoTorsion n)).map_mul σ τ)
    exact h.trans (add_comm _ _)⟩

lemma actual_continuous_group_cocycle_mul (n : F) (χ ψ : continuousCocycles n) :
    continuousGroupCocycle n (χ*ψ)=continuousGroupCocycle n χ+continuousGroupCocycle n ψ := by
  apply Subtype.ext
  funext σ
  rfl

def continuousHOneMap (n : F) : continuousCocycles n →* Multiplicative (H1 (actualTwoTorsionRep n)) where
  toFun χ := Multiplicative.ofAdd (H1π (actualTwoTorsionRep n) (continuousGroupCocycle n χ))
  map_one' := by
    have h : continuousGroupCocycle n 1=0 := by apply Subtype.ext; funext σ; rfl
    change Multiplicative.ofAdd (H1π _ (continuousGroupCocycle n 1))=1
    rw [h,map_zero]
    rfl
  map_mul' χ ψ := by
    change Multiplicative.ofAdd (H1π _ (continuousGroupCocycle n (χ*ψ)))=
      Multiplicative.ofAdd (H1π _ (continuousGroupCocycle n χ))*Multiplicative.ofAdd (H1π _ (continuousGroupCocycle n ψ))
    rw [actual_continuous_group_cocycle_mul,map_add]
    rfl

lemma actual_continuous_hone_injective (n : F) : Function.Injective (continuousHOneMap n) := by
  intro χ ψ h
  have he := congrArg Multiplicative.toAdd h
  change H1π _ (continuousGroupCocycle n χ)=H1π _ (continuousGroupCocycle n ψ) at he
  rw [H1π_eq_iff,coboundaries₁_eq_bot_of_isTrivial,Submodule.mem_bot,sub_eq_zero] at he
  apply Subtype.ext
  apply MonoidHom.ext
  intro σ
  exact congrArg Multiplicative.ofAdd (congrFun he σ)

end ActualTwoDescentContinuousHOneEmbedding318
