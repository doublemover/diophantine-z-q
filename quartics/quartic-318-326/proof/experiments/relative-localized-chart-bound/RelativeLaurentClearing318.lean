module
public import RelativeLaurentScalar318
public section
noncomputable section
namespace RelativeLaurentClearing318
open LaurentPolynomial RelativeLaurentScalar318
set_option maxHeartbeats 600000
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module (LaurentPolynomial R) M]
local instance : Module R M := coefficientModule R M
variable (Q : Submodule R M)

/-- Clearing only positive Laurent denominators in the actual original
module. No basis, domain, reducedness or field assumption appears. -/
def Bounded (x : M) : Prop := ∃ b : ℤ, (T (-b) : LaurentPolynomial R) • x ∈ Q

lemma lower_bound
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    {b d : ℤ} (hbd : b ≤ d) {x : M} (hx : (T (-b) : LaurentPolynomial R) • x ∈ Q) :
    (T (-d) : LaurentPolynomial R) • x ∈ Q := by
  have h := hQ (b-d) (by omega) _ hx
  rw [shift_add] at h
  have he : (b-d)+(-b) = -d := by omega
  simpa only [he] using h

lemma bounded_add
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    {x y : M} (hx : Bounded R M Q x) (hy : Bounded R M Q y) : Bounded R M Q (x+y) := by
  obtain ⟨b,hb⟩ := hx
  obtain ⟨d,hd⟩ := hy
  refine ⟨max b d,?_⟩
  rw [smul_add]
  exact Q.add_mem (lower_bound R M Q hQ (le_max_left _ _) hb)
    (lower_bound R M Q hQ (le_max_right _ _) hd)

lemma bounded_smul
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (r : LaurentPolynomial R) {x : M} (hx : Bounded R M Q x) : Bounded R M Q (r • x) := by
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [add_smul]
      exact bounded_add R M Q hQ hp hq
  | C_mul_T a c =>
      obtain ⟨b,hb⟩ := hx
      refine ⟨b+a,?_⟩
      rw [shift_constant]
      have he : -(b+a)+a = -b := by omega
      rw [he]
      exact Q.smul_mem c hb

/-- The bounded elements form an actual Laurent submodule. The use of
Laurent finite support is explicit in bounded_smul, including nonreduced R. -/
def boundedSubmodule
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q) :
    Submodule (LaurentPolynomial R) M where
  carrier := Bounded R M Q
  zero_mem' := ⟨0,by simpa only [smul_zero] using Q.zero_mem⟩
  add_mem' := bounded_add R M Q hQ
  smul_mem' r x hx := bounded_smul R M Q hQ r hx

/-- If localization of the original negative chart spans the whole overlap,
EVERY original overlap element admits an actual denominator bound. -/
lemma exists_bound
    (hQ : ∀ (a : ℤ), a ≤ 0 → ∀ x ∈ Q, (T a : LaurentPolynomial R) • x ∈ Q)
    (hspan : Submodule.span (LaurentPolynomial R) (Q : Set M) = ⊤) (x : M) :
    Bounded R M Q x := by
  have hs : Submodule.span (LaurentPolynomial R) (Q : Set M) ≤ boundedSubmodule R M Q hQ := by
    apply Submodule.span_le.mpr
    intro y hy
    refine ⟨0,?_⟩
    simpa only [neg_zero,T_zero,one_smul] using hy
  rw [hspan] at hs
  exact hs (Submodule.mem_top : x ∈ (⊤ : Submodule (LaurentPolynomial R) M))
end RelativeLaurentClearing318
