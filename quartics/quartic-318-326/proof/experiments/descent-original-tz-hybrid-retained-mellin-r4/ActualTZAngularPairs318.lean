module
public import ActualTZLiteralMellinTensor318
import all Mathlib.MeasureTheory.MeasurableSpace.Embedding
import all Mathlib.Logic.Equiv.Prod
public section
noncomputable section
namespace ActualTZAngularPairs318
open MeasureTheory
open scoped Topology
open ActualTZLiteralMellinTensor318

/-- Exact original slot convention. The first component of the
pair is the original d/Bool.true, not whichever appears first in
an arbitrary finite enumeration. -/
def boolSum (I : Type*) : Slot I≃I⊕I where
  toFun j := if j.2 then .inl j.1 else .inr j.1
  invFun := fun
    | .inl i => (i,true)
    | .inr i => (i,false)
  left_inv j := by rcases j with ⟨i,b⟩; cases b <;> rfl
  right_inv j := by cases j <;> rfl

def pairing (I : Type*) : (Slot I→ℝ)≃ᵐ(I→(ℝ×ℝ)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : I⊕I=>ℝ) (boolSum I)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕I=>ℝ))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).symm

theorem pairing_apply (I : Type*) (ξ : Slot I→ℝ) (i : I) :
    pairing I ξ i=(ξ (i,true),ξ (i,false)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : I⊕I=>ℝ) (boolSum I)
  change (e ξ (.inl i),e ξ (.inr i))=(ξ (i,true),ξ (i,false))
  exact Prod.ext
    (MeasurableEquiv.piCongrLeft_apply_apply (boolSum I) ξ (i,true))
    (MeasurableEquiv.piCongrLeft_apply_apply (boolSum I) ξ (i,false))

theorem pairing_preserves (I : Type*) [Fintype I] :
    MeasurePreserving (pairing I) (μ I)
      (Measure.pi fun _ : I=>(volume : Measure ℝ).prod volume) := by
  let m (_ : I⊕I) : Measure ℝ := volume
  let v (_ : I) : Measure ℝ := volume
  have h₁ := measurePreserving_piCongrLeft m (boolSum I)
  have h₂ := measurePreserving_sumPiEquivProdPi m
  have h₃ := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I v v).symm
  exact h₃.comp (h₂.comp h₁)

end ActualTZAngularPairs318
