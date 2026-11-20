module
public import SelectedShortOrdinaryRatio318
public import Mathlib.RingTheory.Derivation.Basic
public section
noncomputable section

namespace SelectedShortTameContact318
variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O A]
variable (a₀ : O) (z : A) (q : Aˣ)
local notation "a" => algebraMap O A a₀
variable (hq : (q:A) = 4*a^3+27*z^2)

@[expose] def model : WeierstrassCurve A := ⟨0,0,0,a,z⟩
instance : (model a₀ z).IsShortNF := ⟨rfl,rfl,rfl⟩

theorem discriminant :
    (model a₀ z).Δ = -16*(4*a^3+27*z^2) := by
  simp only [model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

include hq in
theorem elliptic (h16 : IsUnit (-16:A)) : (model a₀ z).IsElliptic :=
  ⟨by rw [discriminant,←hq]; exact h16.mul q.isUnit⟩

abbrev jValue := (1728*(4*a^3))*(↑q⁻¹:A)
abbrev contactUnit : A := -(1728*27)*(↑q⁻¹:A)
abbrev derivativeUnit : A := -(1728*(4*a^3)*54)*(↑q⁻¹:A)^2

/-- Exact invariant of the genuine short model, in the same normalization
of j, not a coordinate up to a scale. -/
theorem actual_j (h16 : IsUnit (-16:A)) :
    letI := elliptic a₀ z q hq h16
    (model a₀ z).j = jValue a₀ q := by
  letI := elliptic a₀ z q hq h16
  apply (h16.mul q.isUnit).mul_right_cancel
  have h := (SelectedShortOrdinaryRatio318.c4_cube_j (model a₀ z)).symm
  rw [discriminant,SelectedShortOrdinaryRatio318.short_c4,←hq] at h
  calc
    _ = (-48*a)^3 := h
    _ = (1728*(4*a^3)*(-16))*((↑q⁻¹:A)*(q:A)) := by
      rw [Units.inv_mul,mul_one]
      ring
    _ = _ := by unfold jValue; ring

/-- Exact quadratic contact of j about 1728 on the same fixed-a short
deformation chart. -/
include hq in
theorem j_contact :
    jValue a₀ q-1728 = contactUnit q*z^2 := by
  calc
    _ = (1728*(4*a^3)-1728*(q:A))*(↑q⁻¹:A) := by
      unfold jValue
      rw [sub_mul,mul_assoc (1728:A) (q:A) (↑q⁻¹:A),Units.mul_inv,mul_one]
    _ = _ := by rw [hq]; unfold contactUnit; ring

variable (δ : Derivation O A A) (hz : δ z = 1)
include hz hq in
theorem j_derivative :
    δ (jValue a₀ q) = derivativeUnit a₀ q*z := by
  have hq' : δ (q:A) = 54*z := by
    rw [hq]
    simp [Derivation.leibniz_pow,hz,smul_eq_mul,nsmul_eq_mul] <;> ring
  have hi : δ (↑q⁻¹:A) = -(↑q⁻¹:A)^2*δ (q:A) := by
    simpa only [smul_eq_mul] using δ.leibniz_of_mul_eq_one (Units.inv_mul q)
  have ha : δ (1728*(4*a^3)) = 0 := by simp [Derivation.leibniz_pow,smul_eq_mul]
  unfold jValue derivativeUnit
  rw [δ.leibniz,ha,hi,hq']
  simp only [smul_eq_mul,mul_zero,add_zero]
  ring

theorem contact_isUnit (h2 : IsUnit (2:A)) (h3 : IsUnit (3:A)) :
    IsUnit (contactUnit q) := by
  have h : (-(1728*27):A) = -((2:A)^6*(3:A)^6) := by norm_num
  change IsUnit ((-(1728*27):A)*(↑q⁻¹:A))
  rw [h]
  exact (((h2.pow 6).mul (h3.pow 6)).neg).mul (q⁻¹).isUnit

theorem derivative_isUnit (h2 : IsUnit (2:A)) (h3 : IsUnit (3:A)) (ha : IsUnit a) :
    IsUnit (derivativeUnit a₀ q) := by
  have hn : (-(1728*(4*a^3)*54):A) = -(((2:A)^9*(3:A)^6)*a^3) := by ring
  change IsUnit ((-(1728*(4*a^3)*54):A)*(↑q⁻¹:A)^2)
  rw [hn]
  exact ((((h2.pow 9).mul (h3.pow 6)).mul (ha.pow 3)).neg).mul ((q⁻¹).isUnit.pow 2)

end SelectedShortTameContact318

#print axioms SelectedShortTameContact318.actual_j
#print axioms SelectedShortTameContact318.j_contact
#print axioms SelectedShortTameContact318.j_derivative
