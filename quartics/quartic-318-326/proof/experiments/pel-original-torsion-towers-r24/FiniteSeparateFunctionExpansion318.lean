module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public section
noncomputable section
namespace FiniteSeparateFunctionExpansion318
open Set Submodule
variable {K X Y I J : Type*} [Field K] [Fintype I] [Fintype J]

/-- Actual separate finite spans give one constant double expansion.
The first family is independent as FUNCTIONS on the entire original X.
No integration, interchange of infinite sums, or unproved tensor-family
completeness is used: coordinate functionals lie in the span of genuine
point evaluations on a finite-dimensional coefficient space. -/
theorem exists_double_expansion (b : I → X → K) (d : J → Y → K)
    (hb : LinearIndependent K b) (F : X → Y → K)
    (hfirst : ∀ y, ∃ c : I → K, ∀ x, F x y = ∑ i, c i * b i x)
    (hsecond : ∀ x, ∃ c : J → K, ∀ y, F x y = ∑ j, c j * d j y) :
    ∃ a : I → J → K, ∀ x y,
      F x y = ∑ i, ∑ j, a i j * b i x * d j y := by
  classical
  choose c hc using hfirst
  let ev (x : X) : (I → K) →ₗ[K] K :=
    { toFun := fun v => ∑ i, v i * b i x
      map_add' := by intro v w; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a v; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum] }
  let T : Module.Dual K (I → K) →ₗ[K] (Y → K) :=
    { toFun := fun l y => l (c y)
      map_add' := by intro l m; rfl
      map_smul' := by intro a l; rfl }
  let V := Submodule.span K (Set.range d)
  have hrows : Submodule.span K (Set.range ev) ≤ V.comap T := by
    apply Submodule.span_le.mpr
    rintro l ⟨x,rfl⟩
    change (fun y => ev x (c y)) ∈ V
    obtain ⟨a,ha⟩ := hsecond x
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨a,?_⟩
    funext y
    change (∑ j, a j • d j) y = ev x (c y)
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      (ha y).symm.trans (hc y x)
  have hcoordinate (i : I) : (LinearMap.proj i : (I → K) →ₗ[K] K) ∈
      Submodule.span K (Set.range ev) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have hall (x : X) : ev x v = 0 := (Submodule.mem_iInf.mp hv x)
    have hlin : ∑ i, v i • b i = 0 := by
      funext x
      have hx := hall x
      change (∑ i, v i * b i x) = 0 at hx
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hx
    change v i = 0
    exact (Fintype.linearIndependent_iff.mp hb v hlin) i
  have hcoeff (i : I) : (fun y => c y i) ∈ V := hrows (hcoordinate i)
  have hex (i : I) : ∃ a : J → K, ∀ y, c y i = ∑ j, a j * d j y := by
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hcoeff i)
    refine ⟨a,?_⟩
    intro y
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using (congrFun ha y).symm
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x y
  rw [hc y x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i y,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring
end FiniteSeparateFunctionExpansion318
