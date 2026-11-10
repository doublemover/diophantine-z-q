module
public import OriginalNegativePoleUniqueness318
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.LinearMap.Rat

public section
noncomputable section
namespace OriginalOverlapResidues318
open OriginalNegativePoleUniqueness318 RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
abbrev Residues := (ℕ × ThreeIndex) →₀ ℚ

@[expose] def negativeEvaluation : Residues →ₗ[ℚ] OverlapRing c :=
  Finsupp.linearCombination ℚ (fun p : ℕ × ThreeIndex => poleTerm c 1 (p.1+1) p.2)

@[expose] def infinityLinear : InfinityRing c →ₗ[ℚ] OverlapRing c :=
  (InfinityOverlapLocalization318.toOpen c).toAddMonoidHom.toRatLinearMap

/-- Rational linearity of additive homomorphisms identifies the native
rational module action with multiplication by the SAME coefficient map. -/
private theorem rational_scalar {A : Type*} [Ring A] [Module ℚ A]
    (φ : ℚ →+* A) (q : ℚ) (z : A) : q • z = φ q * z := by
  have hq : q • (1 : A) = φ q := by
    have h := map_rat_smul φ q (1 : ℚ)
    simpa only [smul_eq_mul, mul_one, map_one] using h.symm
  have h := map_rat_smul (AddMonoidHom.mulRight z) q (1 : A)
  change (q • (1 : A)) * z = q • ((1 : A) * z) at h
  rw [one_mul] at h
  exact h.symm.trans (congrArg (fun a : A => a * z) hq)

private theorem scalar_pole (q : ℚ) (k : ℕ) (i : ThreeIndex) :
    q • poleTerm c 1 k i = poleTerm c q k i := by
  simp only [poleTerm, map_one, one_mul]
  exact (rational_scalar (algebraMap ℚ (OverlapRing c)) q _).trans
    (mul_assoc _ _ _).symm

theorem evaluation_single (k : ℕ) (i : ThreeIndex) (q : ℚ) :
    negativeEvaluation c (Finsupp.single (k,i) q) = poleTerm c q (k+1) i := by
  rw [negativeEvaluation, Finsupp.linearCombination_single]
  exact scalar_pole c q (k+1) i

theorem evaluation_rectangle (f : Residues) (N : ℕ)
    (hf : f.support ⊆ (Finset.range N).product Finset.univ) :
    negativeEvaluation c f = negativeSum c (fun k i => f (k,i)) N := by
  classical
  have hs : (∑ p ∈ f.support, f p • poleTerm c 1 (p.1+1) p.2) =
      ∑ p ∈ (Finset.range N).product Finset.univ, f p • poleTerm c 1 (p.1+1) p.2 := by
    apply Finset.sum_subset hf
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp,zero_smul]
  change (∑ p ∈ f.support, f p • poleTerm c 1 (p.1+1) p.2) = _
  calc
    _ = ∑ p ∈ (Finset.range N).product Finset.univ,
        f p • poleTerm c 1 (p.1+1) p.2 := hs
    _ = ∑ k ∈ Finset.range N, ∑ i : ThreeIndex,
        f (k,i) • poleTerm c 1 (k+1) i :=
      Finset.sum_product (Finset.range N) Finset.univ
        (fun p : ℕ × ThreeIndex => f p • poleTerm c 1 (p.1+1) p.2)
    _ = negativeSum c (fun k i => f (k,i)) N := by
      unfold negativeSum
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact scalar_pole c (f (k,i)) (k+1) i

/-- A finite original negative principal part has no nonzero infinity-regular
representative. This supplies actual coefficient uniqueness, not a genus count. -/
theorem negative_eq_regular_implies_zero (f : Residues) (b : InfinityRing c)
    (h : negativeEvaluation c f = infinityLinear c b) : f = 0 := by
  classical
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range (f.support.image Prod.fst)
  have hs : f.support ⊆ (Finset.range N).product Finset.univ := by
    intro p hp
    exact Finset.mem_product.mpr ⟨hN (Finset.mem_image.mpr ⟨p,hp,rfl⟩),Finset.mem_univ _⟩
  rw [evaluation_rectangle c f N hs] at h
  have hz := negative_coefficients_zero c (fun k i => f (k,i)) N b h
  ext p
  by_cases hp : p ∈ f.support
  · exact hz p.1 (Finset.mem_range.mp (Finset.mem_product.mp (hs hp)).1) p.2
  · exact Finsupp.notMem_support_iff.mp hp

@[expose] def presentation : (Residues × InfinityRing c) →ₗ[ℚ] OverlapRing c :=
  (negativeEvaluation c).comp (LinearMap.fst ℚ Residues (InfinityRing c)) +
    (infinityLinear c).comp (LinearMap.snd ℚ Residues (InfinityRing c))

theorem presentation_apply (f : Residues) (b : InfinityRing c) :
    presentation c (f,b) = negativeEvaluation c f + infinityLinear c b := rfl

theorem positive_pole_in_range (q : ℚ) (k : ℕ) (i : ThreeIndex) (hk : 0 < k) :
    poleTerm c q k i ∈ (negativeEvaluation c).range := by
  refine ⟨Finsupp.single (k-1,i) q,?_⟩
  rw [evaluation_single]
  have he : k-1+1 = k := by omega
  rw [he]

theorem principal_product_in_range (P : Polynomial ℚ) (n : ℕ)
    (hP : P.degree < (n : WithBot ℕ)) (i : ThreeIndex) :
    principalTerm c P n * InfinityOverlapLocalization318.toOpen c
      (ContactHOneOrderBases318.infinityBasis c i) ∈ (negativeEvaluation c).range := by
  rw [ContactPrincipalCoefficientExpansion318.principalTerm_expansion c P n hP,Finset.sum_mul]
  apply (negativeEvaluation c).range.sum_mem
  intro j hj
  apply positive_pole_in_range c (P.coeff j) (n-j) i
  have hlt := ContactPrincipalCoefficientExpansion318.support_lt_pole P n hP j hj
  omega

/-- The complete original overlap is the sum of its finite negative principal
parts and its actual infinity-ring image. -/
theorem presentation_surjective : Function.Surjective (presentation c) := by
  intro z
  obtain ⟨n,R,b,hR,hr⟩ := ContactWholePrincipalReduction318.reduction c z
  have hs : (∑ i, principalTerm c (R i) n * InfinityOverlapLocalization318.toOpen c
      (ContactHOneOrderBases318.infinityBasis c i)) ∈ (negativeEvaluation c).range := by
    exact (negativeEvaluation c).range.sum_mem (fun i _ => principal_product_in_range c (R i) n (hR i) i)
  obtain ⟨f,hf⟩ := hs
  refine ⟨(f,b),?_⟩
  rw [presentation_apply,hf]
  exact hr.symm

theorem kernel_le_first : (presentation c).ker ≤ (LinearMap.fst ℚ Residues (InfinityRing c)).ker := by
  rintro ⟨f,b⟩ h
  change negativeEvaluation c f + infinityLinear c b = 0 at h
  change f = 0
  apply negative_eq_regular_implies_zero c f (-b)
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

/-- Canonical full negative coefficient list on the original overlap ring.
Its construction proves independence of the chosen pole bound and remainder. -/
@[expose] def residues : OverlapRing c →ₗ[ℚ] Residues :=
  (presentation c).liftOfSurjective (presentation_surjective c)
    ⟨LinearMap.fst ℚ Residues (InfinityRing c),kernel_le_first c⟩

theorem residues_presentation (f : Residues) (b : InfinityRing c) :
    residues c (negativeEvaluation c f + infinityLinear c b) = f := by
  change ((presentation c).liftOfSurjective _) ⟨_,kernel_le_first c⟩ (presentation c (f,b)) = f
  rw [LinearMap.equivOfSurjective_apply] <;> rfl

theorem residues_negativeEvaluation (f : Residues) : residues c (negativeEvaluation c f) = f := by
  simpa only [map_zero,add_zero] using residues_presentation c f 0

theorem residues_infinity (b : InfinityRing c) : residues c (infinityLinear c b) = 0 := by
  simpa only [map_zero,zero_add] using residues_presentation c 0 b

theorem residues_pole (q : ℚ) (k : ℕ) (i : ThreeIndex) (hk : 0 < k) :
    residues c (poleTerm c q k i) = Finsupp.single (k-1,i) q := by
  have he : k-1+1 = k := by omega
  have hEval : negativeEvaluation c (Finsupp.single (k-1,i) q) = poleTerm c q k i := by
    rw [evaluation_single,he]
  rw [← hEval,residues_negativeEvaluation]

end OriginalOverlapResidues318
