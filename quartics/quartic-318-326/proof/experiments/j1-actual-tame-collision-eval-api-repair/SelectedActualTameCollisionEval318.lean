module
public import SelectedShortTameContact318
public import SelectedCollisionHalfCost318
import all SelectedJOneExactMinorLoss318
public section
noncomputable section
open NumberField SelectedJOneExactMinorLoss318 SelectedShortTameContact318
open SelectedCollisionHalfCost318

namespace SelectedActualTameCollisionEval318
variable {L : Type*} [Field L] [NumberField L] (v : FinitePlace L)
local notation "O" => integralAt v

/-- An actual unit of the v-integral ring has normalization exactly 1;
no assertion about the determinant lattice being a unit is used. -/
theorem localUnit_norm {y : O} (hy : IsUnit y) :
    v (algebraMap O L y) = 1 := by
  obtain ⟨w,rfl⟩ := hy
  have hin : v (algebraMap O L (w:O)) ≤ 1 := (w:O).property
  have hinv : v (algebraMap O L (↑w⁻¹:O)) ≤ 1 := (↑w⁻¹:O).property
  have hmul : v (algebraMap O L (w:O)) * v (algebraMap O L (↑w⁻¹:O)) = 1 := by
    rw [←map_mul,←map_mul,Units.mul_inv] <;> simp only [map_one]
  exact le_antisymm hin
    (hmul.symm.trans_le (mul_le_of_le_one_right (apply_nonneg v _) hinv))

variable {A : Type*} [CommRing A] [Algebra O A]
variable (β : A →ₐ[O] O)

abbrev absolutePoint : A →+* L := (algebraMap O L).comp β.toRingHom

variable (a : O) (z : A) (q : Aˣ)
variable (hq : (q:A) = 4*(algebraMap O A a)^3+27*z^2)
variable (δ : Derivation O A A) (hδ : δ z = 1)
variable (h2 : IsUnit (2:A)) (h3 : IsUnit (3:A)) (ha : IsUnit (algebraMap O A a))
variable (h1 : β (jValue a q) = 1)

include hq hδ h1 h2 h3 ha in
/-- Evaluate the actual short deformation at the same literal j=1
section; the dJ coefficient in its normalized dz frame then contributes
exactly half the normalized 157 contact. -/
theorem at_section (h11 : v (11:L) = 1) :
    -Real.log (v (absolutePoint v β (δ (jValue a q)))) =
      (-Real.log (v (157:L))) / 2 := by
  let E := absolutePoint v β
  have hE : E (jValue a q) = 1 := by
    change algebraMap O L (β (jValue a q)) = 1
    rw [h1,map_one]
  have hc : v (E (contactUnit q)) = 1 :=
    localUnit_norm v ((contact_isUnit q h2 h3).map β.toRingHom)
  have hd : v (E (derivativeUnit a q)) = 1 :=
    localUnit_norm v ((derivative_isUnit a q h2 h3 ha).map β.toRingHom)
  have hC := congrArg E (j_contact a z q hq)
  have hD := congrArg E (j_derivative a z q hq δ hδ)
  simp only [map_sub,map_ofNat,map_mul,map_pow,hE] at hC
  simp only [map_mul] at hD
  have hC' : -(1727:L) = E (contactUnit q) * (E z)^2 := by
    convert hC using 1 <;> norm_num
  exact contact_157 v hc hd h11 hC' hD

end SelectedActualTameCollisionEval318
#print axioms SelectedActualTameCollisionEval318.localUnit_norm
#print axioms SelectedActualTameCollisionEval318.at_section
