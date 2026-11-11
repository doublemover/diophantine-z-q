module
public import Mathlib.AlgebraicGeometry.Properties
public section
noncomputable section
namespace IntegralCompatibleCoefficients318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} [IsIntegral X] {ι : Type u} (U : ι → X.Opens)
  (c : ∀ i,Γ(X,U i)) (t : ∀ i j,Γ(X,U i ⊓ U j)ˣ)
  (hc : ∀ i j,X.presheaf.map (homOfLE inf_le_left).op (c i)=
    (t i j).val*X.presheaf.map (homOfLE inf_le_right).op (c j))
  (hMeet : ∀ i j,Nonempty (U i ⊓ U j))

include hc hMeet in
/-- On an integral scheme, one nonzero compatible line coefficient
forces every coefficient on a nonempty intersecting chart to be nonzero.
This uses actual injectivity of restriction, not just pointwise density. -/
lemma all_nonzero (h : ∃ i,c i≠0) : ∀ i,c i≠0 := by
  obtain ⟨j,hj⟩ := h
  intro i hi
  letI := hMeet i j
  have he := hc i j
  rw [hi,map_zero] at he
  have hr := congrArg (fun x : Γ(X,U i ⊓ U j) => ((t i j)⁻¹).val*x) he
  have hz : X.presheaf.map (homOfLE (show U i ⊓ U j≤U j from inf_le_right)).op (c j)=0 := by
    simpa only [mul_zero,←mul_assoc,Units.inv_val_mul_val,one_mul] using hr.symm
  exact hj (map_injective_of_isIntegral X (homOfLE inf_le_right)
    (hz.trans (map_zero _).symm))
end IntegralCompatibleCoefficients318
