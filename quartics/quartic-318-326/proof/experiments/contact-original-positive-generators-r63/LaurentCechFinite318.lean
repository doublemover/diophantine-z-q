module
public import LaurentTransitionBounds318
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section
noncomputable section
namespace LaurentCechFinite318
open LaurentVectorFiltration318 LaurentTransitionBounds318
universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- The actual two-chart coboundary image, retaining the original transition. -/
@[expose] def boundary (e : V k n ≃ₗ[LaurentPolynomial k] V k n) : Submodule k (V k n) :=
  positive ⊔ negative.map (underlying e)

/-- The actual two-chart first Cech cokernel on this free Laurent module. -/
abbrev H1 (e : V k n ≃ₗ[LaurentPolynomial k] V k n) := V k n ⧸ boundary e

lemma finite_supported {S : Set ℤ} (hS : S.Finite) :
    FiniteDimensional k (supported (k:=k) (n:=n) S) := by
  apply FiniteDimensional.span_of_finite
  have h : {v : V k n | ∃ i : Fin n, ∃ a ∈ S, v = monomial i a} =
      (fun p : Fin n × ℤ => monomial (k:=k) p.1 p.2) '' (Set.univ ×ˢ S) := by
    ext v
    constructor
    · rintro ⟨i,a,ha,rfl⟩
      exact ⟨(i,a),⟨Set.mem_univ _,ha⟩,rfl⟩
    · rintro ⟨⟨i,a⟩,⟨hi,ha⟩,rfl⟩
      exact ⟨i,a,ha,rfl⟩
  rw [h]
  exact (Set.toFinite (Set.univ : Set (Fin n))).prod hS |>.image _

/-- Explicit finite exponent window spanning the actual Cech quotient. -/
lemma boundary_sup_window (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e.symm (monomial i 0) ∈ upper b) :
    boundary e ⊔ supported (Set.Icc (-b+1) (-1)) = ⊤ := by
  apply top_unique
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ (supported_univ v)
  · rintro w ⟨i,a,ha,rfl⟩
    by_cases hp : 0 ≤ a
    · exact (le_sup_left : boundary e ≤ _)
        ((le_sup_left : positive ≤ boundary e) (monomial_mem i a hp))
    · by_cases hn : a+b ≤ 0
      · exact (le_sup_left : boundary e ≤ _)
          ((le_sup_right : negative.map (underlying e) ≤ boundary e)
            (negative_tail e b hb i a hn))
      · exact (le_sup_right : supported (Set.Icc (-b+1) (-1)) ≤ _)
          (monomial_mem i a (by constructor <;> omega))
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    exact Submodule.smul_mem _ c hx

/-- The finite window maps onto the quotient of the original Laurent module;
the map is the restriction of the original quotient map. -/
lemma window_surjective (e : V k n ≃ₗ[LaurentPolynomial k] V k n)
    (b : ℤ) (hb : ∀ i : Fin n, e.symm (monomial i 0) ∈ upper b) :
    Function.Surjective ((boundary e).mkQ.comp
      (supported (k:=k) (n:=n) (Set.Icc (-b+1) (-1))).subtype) := by
  intro q
  obtain ⟨v,rfl⟩ := (boundary e).mkQ_surjective q
  have hv : v ∈ boundary e ⊔ supported (Set.Icc (-b+1) (-1)) := by
    rw [boundary_sup_window e b hb]
    trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
  refine ⟨⟨y,hy⟩,?_⟩
  change (boundary e).mkQ y = (boundary e).mkQ v
  have hx0 : (boundary e).mkQ x = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  rw [← hxy,map_add,hx0,zero_add]

/-- Finite-dimensionality follows for every invertible Laurent transition,
without an externally supplied exponent bound or finite spanning hypothesis. -/
theorem finite_h1 (e : V k n ≃ₗ[LaurentPolynomial k] V k n) :
    FiniteDimensional k (H1 e) := by
  obtain ⟨b,hb⟩ := exists_column_bound e.symm
  letI := finite_supported (k:=k) (n:=n) (Set.finite_Icc (-b+1) (-1))
  exact Module.Finite.of_surjective
    ((boundary e).mkQ.comp (supported (Set.Icc (-b+1) (-1))).subtype)
    (window_surjective e b hb)
end LaurentCechFinite318
