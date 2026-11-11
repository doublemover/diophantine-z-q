module
public import PELPrincipalOrderCoordinates318
public import PELQuaternionRealRepresentation318
public section
noncomputable section
namespace PELOriginalComplementaryOrder318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318
open PELQuaternionRealRepresentation318 QuaternionAlgebra

/-- The complementary element stays in the SAME half-integral order.
Its real matrix is the transpose of the adjugate of the original matrix. -/
@[expose] def complementCoordinates (x : Coordinates) : Coordinates :=
  ![x 0+x 2,x 1+x 3,-x 2,-x 3]
@[expose] def complement (a : order) : order :=
  coordinatesEquiv (complementCoordinates (coordinatesEquiv.symm a))

theorem complement_value (a : order) :
    (complement a : B)=rosati (star (a:B)) := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  simp only [complement,AddEquiv.symm_apply_apply,coordinatesEquiv_value,
    rosati_coordinates]
  ext <;> simp [complementCoordinates,embed] <;> ring

/-- Literal integer trace weight, with every denominator of the original
order basis accounted for. -/
@[expose] def weight (x : Coordinates) : ℤ :=
  2*x 0^2+2*x 0*x 2+3*x 2^2+420*x 1^2+420*x 1*x 3+126*x 3^2

theorem weight_formula (x : Coordinates) :
    (weight x : ℚ)=2*((embed x).re^2+210*(embed x).imI^2+
      5*(embed x).imJ^2+1050*(embed x).imK^2) := by
  simp only [weight,embed]
  push_cast
  ring

theorem weight_nonneg (x : Coordinates) : 0 ≤ weight x := by
  have h : (0:ℚ) ≤ (weight x:ℚ) := by rw [weight_formula]; positivity
  exact_mod_cast h

@[expose] def degree (a : order) : ℕ :=
  (weight (coordinatesEquiv.symm a)).toNat

theorem degree_cast (a : order) :
    (degree a : ℤ)=weight (coordinatesEquiv.symm a) :=
  Int.toNat_of_nonneg (weight_nonneg _)

theorem degree_formula (a : order) :
    (degree a : ℝ)=2*((((a:B).re:ℝ))^2+210*(((a:B).imI:ℝ))^2+
      5*(((a:B).imJ:ℝ))^2+1050*(((a:B).imK:ℝ))^2) := by
  obtain ⟨x,rfl⟩ := coordinatesEquiv.surjective a
  have hc := degree_cast (coordinatesEquiv x)
  simp only [AddEquiv.symm_apply_apply] at hc
  have hw := weight_formula x
  have hr : (weight x:ℝ)=2*(((embed x).re:ℝ)^2+210*((embed x).imI:ℝ)^2+
      5*((embed x).imJ:ℝ)^2+1050*((embed x).imK:ℝ)^2) := by exact_mod_cast hw
  have hn : (degree (coordinatesEquiv x):ℝ)=(weight x:ℝ) := by exact_mod_cast hc
  exact hn.trans hr

theorem matrix_complement (a : order) :
    representation (complement a)=
      !![representation a 1 1,-representation a 1 0;
         -representation a 0 1,representation a 0 0] := by
  rw [complement_value,rosati_coordinates]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [representation,matrix] <;> ring

theorem matrix_weight (a : order) :
    (representation a 0 0)^2+(representation a 0 1)^2+
      (representation a 1 0)^2+(representation a 1 1)^2=(degree a:ℝ) := by
  rw [degree_formula]
  simp [representation,matrix]
  ring_nf
  simp only [alpha_sq,beta_sq]
  ring
end PELOriginalComplementaryOrder318
