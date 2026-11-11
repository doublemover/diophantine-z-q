module
public import RelativeLaurentWindowPresentation318
public import Mathlib.LinearAlgebra.Quotient.Defs
public section
noncomputable section
namespace RelativeProjectiveFreeCech318
open RelativeLaurentVectorFiltration318
set_option maxHeartbeats 800000
universe u
variable (R : Type u) [CommRing R] (r n : ℕ)

/-- The literal Cech boundary of r copies of projective O(-n): finite
nonnegative exponents and reciprocal exponents at most -n. -/
@[expose] def boundary : Submodule R (V R r) := positive ⊔ upper (-(n : ℤ))
@[expose] def window : Submodule R (V R r) := supported (Set.Icc (-(n : ℤ)+1) (-1))

lemma boundary_sup_window : boundary R r n ⊔ window R r n = ⊤ := by
  apply top_unique
  intro v _
  refine Submodule.span_induction ?_ ?_ ?_ ?_ (supported_univ v)
  · rintro w ⟨i,a,_,rfl⟩
    by_cases hp : 0 ≤ a
    · exact (le_sup_left : boundary R r n ≤ _) ((le_sup_left : positive ≤ boundary R r n)
        (monomial_mem i a hp))
    · by_cases hn : a ≤ -(n : ℤ)
      · exact (le_sup_left : boundary R r n ≤ _) ((le_sup_right : upper (-(n : ℤ)) ≤ boundary R r n)
          (monomial_mem i a hn))
      · exact (le_sup_right : window R r n ≤ _) (monomial_mem i a (by constructor <;> omega))
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    exact Submodule.smul_mem _ a hx

lemma boundary_coeff (v : V R r) (hv : v ∈ boundary R r n) (i : Fin r) (a : ℤ)
    (ha : a ∈ Set.Icc (-(n : ℤ)+1) (-1)) : (v i).coeff a = 0 := by
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  have hx0 := coeff_eq_zero (k := R) hx i a (by
    change ¬ 0 ≤ a
    have h := ha.2
    omega)
  have hy0 := coeff_eq_zero (k := R) hy i a (by
    change ¬ a ≤ -(n : ℤ)
    have h := ha.1
    omega)
  simpa using congrArg₂ (·+·) hx0 hy0

@[expose] def windowMap : window R r n →ₗ[R] (V R r ⧸ boundary R r n) :=
  (boundary R r n).mkQ.comp (window R r n).subtype

lemma windowMap_surjective : Function.Surjective (windowMap R r n) := by
  intro q
  obtain ⟨v,rfl⟩ := (boundary R r n).mkQ_surjective q
  have hv : v ∈ boundary R r n ⊔ window R r n := by rw [boundary_sup_window]; trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
  refine ⟨⟨y,hy⟩,?_⟩
  change (boundary R r n).mkQ y = (boundary R r n).mkQ v
  have hx0 : (boundary R r n).mkQ x = 0 := by
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact hx
  rw [← hxy,map_add,hx0,zero_add]

lemma windowMap_injective : Function.Injective (windowMap R r n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply Subtype.ext
  have hb : (x : V R r) ∈ boundary R r n := (Submodule.Quotient.mk_eq_zero _).mp hx
  ext i a
  by_cases ha : a ∈ Set.Icc (-(n : ℤ)+1) (-1)
  · exact boundary_coeff R r n x hb i a ha
  · exact coeff_eq_zero (k := R) x.property i a ha

/-- Actual original quotient is identified with the finite Laurent
window through the unchanged quotient map; both infinite tails are removed. -/
@[expose] def equivalence : window R r n ≃ₗ[R] (V R r ⧸ boundary R r n) :=
  LinearEquiv.ofBijective (windowMap R r n) ⟨windowMap_injective R r n,windowMap_surjective R r n⟩

lemma finitePresentation : Module.FinitePresentation R (V R r ⧸ boundary R r n) := by
  letI : Module.FinitePresentation R (window R r n) :=
    RelativeLaurentWindowPresentation318.finitePresentation R r _ (Set.finite_Icc _ _)
  exact Module.FinitePresentation.of_equiv (equivalence R r n)
end RelativeProjectiveFreeCech318
