module
public import OriginalPrincipalCocycleRows318
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace OriginalNonreducedCocycleSplit318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite OriginalPrincipalLocalization318
open OriginalPrincipalCocycleRows318
open scoped BigOperators
universe u v
variable (X : Scheme.{u}) [hX : IsAffine X] {ι : Type v} [Fintype ι]
  (f : ι → Γ(X,⊤))

/-- Powers of the original principal-cover equations still generate the
unit ideal. The finite partition is over the original global section ring. -/
lemma power_coefficients (h : Ideal.span (Set.range f) = ⊤) (N : ℕ) :
    ∃ w : ι → Γ(X,⊤), ∑ i, w i * f i ^ N = 1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  have hN := Ideal.span_pow_eq_top (Set.range f) h N
  rw [← Set.range_comp] at hN
  change Ideal.span (Set.range fun i => f i ^ N) = ⊤ at hN
  rw [hN]
  trivial

include hX in
/-- Every additive structure-sheaf cocycle on an actual finite principal
unit-ideal cover of an arbitrary affine scheme splits by ORIGINAL local
sections. Torsion is killed explicitly; neither integrality nor reducedness
nor injection into a fraction field is assumed. -/
theorem split (hcover : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, Γ(X,V X f i j)) (hc : Cocycle X f c) :
    ∃ b : ∀ i, Γ(X,U X f i), ∀ i j,
      c i j = res X (left X f i j) (b i) - res X (right X f i j) (b j) := by
  classical
  obtain ⟨N,a,ha⟩ := OriginalPrincipalCocycleRows318.rows X f c hc
  obtain ⟨w,hw⟩ := power_coefficients X f hcover N
  let b (j : ι) : Γ(X,U X f j) := -∑ i, coefficient X (U X f j) (w i) * a i j
  refine ⟨b,fun j k => ?_⟩
  have hsum : ∑ i, coefficient X (V X f j k) (w i) *
      (coefficient X (V X f j k) (f i))^N = 1 := by
    have h := congrArg (coefficient X (V X f j k)) hw
    simpa only [map_sum,map_mul,map_pow,map_one] using h
  symm
  calc
    _ = ∑ i, coefficient X (V X f j k) (w i) *
        (res X (right X f j k) (a i k) - res X (left X f j k) (a i j)) := by
      dsimp [b]
      simp only [map_neg,map_sum,map_mul,res_coefficient]
      rw [neg_sub_neg,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, (coefficient X (V X f j k) (w i) *
        (coefficient X (V X f j k) (f i))^N) * c j k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ha,mul_assoc]
    _ = c j k := by rw [← Finset.sum_mul,hsum,one_mul]

include hX in
/-- The unit-ideal premise follows from the ACTUAL topological cover,
including empty principal opens. -/
theorem split_of_cover (hcover : (⨆ i, U X f i) = ⊤)
    (c : ∀ i j, Γ(X,V X f i j)) (hc : Cocycle X f c) :
    ∃ b : ∀ i, Γ(X,U X f i), ∀ i j,
      c i j = res X (left X f i j) (b i) - res X (right X f i j) (b j) := by
  apply split X f ?_ c hc
  apply (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mp
  have he : (⨆ g : Set.range f, X.basicOpen (g : Γ(X,⊤))) = ⨆ i, U X f i := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨g,⟨i,rfl⟩⟩
      exact le_iSup (U X f) i
    · apply iSup_le
      intro i
      exact le_iSup (fun g : Set.range f => X.basicOpen (g : Γ(X,⊤))) ⟨f i,⟨i,rfl⟩⟩
  exact he.trans hcover
end OriginalNonreducedCocycleSplit318
