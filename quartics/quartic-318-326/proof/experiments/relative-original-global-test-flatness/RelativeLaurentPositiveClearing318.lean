module
public import RelativeLaurentClearing318
public section
noncomputable section
namespace RelativeLaurentPositiveClearing318
open LaurentPolynomial RelativeLaurentScalar318
set_option maxHeartbeats 600000
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (P : Submodule R M)
@[expose] def Bounded (x : M) : Prop := ∃ b : ℤ, (T b : LaurentPolynomial R) • x ∈ P

lemma upper_bound
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    {b d : ℤ} (hbd : b ≤ d) {x : M} (hx : (T b : LaurentPolynomial R) • x ∈ P) :
    (T d : LaurentPolynomial R) • x ∈ P := by
  have h := hP (d-b) (by omega) _ hx
  rw [shift_add] at h
  simpa only [sub_add_cancel] using h

lemma bounded_add
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    {x y : M} (hx : Bounded R M P x) (hy : Bounded R M P y) : Bounded R M P (x+y) := by
  obtain ⟨b,hb⟩ := hx
  obtain ⟨d,hd⟩ := hy
  refine ⟨max b d,?_⟩
  rw [smul_add]
  exact P.add_mem (upper_bound R M P hP (le_max_left _ _) hb)
    (upper_bound R M P hP (le_max_right _ _) hd)

lemma bounded_smul
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (r : LaurentPolynomial R) {x : M} (hx : Bounded R M P x) : Bounded R M P (r • x) := by
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [add_smul]
      exact bounded_add R M P hP hp hq
  | C_mul_T a c =>
      obtain ⟨b,hb⟩ := hx
      refine ⟨b-a,?_⟩
      rw [shift_constant,sub_add_cancel]
      exact P.smul_mem c hb

def boundedSubmodule
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P) :
    Submodule (LaurentPolynomial R) M where
  carrier := Bounded R M P
  zero_mem' := ⟨0,by simpa only [smul_zero] using P.zero_mem⟩
  add_mem' := bounded_add R M P hP
  smul_mem' r x hx := bounded_smul R M P hP r hx

/-- Genuine denominator clearing in the positive chart, with no
Noetherian, reduced, free or field hypothesis on the coefficient ring. -/
lemma exists_bound
    (hP : ∀ (a : ℤ), 0 ≤ a → ∀ x ∈ P, (T a : LaurentPolynomial R) • x ∈ P)
    (hspan : Submodule.span (LaurentPolynomial R) (P : Set M) = ⊤) (x : M) :
    Bounded R M P x := by
  have hs : Submodule.span (LaurentPolynomial R) (P : Set M) ≤ boundedSubmodule R M P hP := by
    apply Submodule.span_le.mpr
    intro y hy
    refine ⟨0,?_⟩
    change (T 0 : LaurentPolynomial R) • y ∈ P
    rw [T_zero,one_smul]
    exact hy
  rw [hspan] at hs
  exact hs (Submodule.mem_top : x ∈ (⊤ : Submodule (LaurentPolynomial R) M))
end RelativeLaurentPositiveClearing318
