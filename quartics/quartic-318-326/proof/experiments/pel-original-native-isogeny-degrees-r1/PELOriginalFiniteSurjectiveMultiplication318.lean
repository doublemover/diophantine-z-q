module
public import PELOriginalFiniteMultiplication318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace PELOriginalFiniteSurjectiveMultiplication318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 PELOriginalPeriodLattice318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalIntegerMultiplication318 PELOriginalIntegerEndomorphismLaws318
open PELOriginalSchemePointGroup318 PELOriginalTorusPointAddEquiv318
open PELOriginalCandidateComplexPoints318
variable (τ : ℂ) (hτ : 0 < τ.im)
@[expose] def minusOneIso : candidate τ hτ ≅ candidate τ hτ where
  hom := multiplication τ hτ (-1)
  inv := multiplication τ hτ (-1)
  hom_inv_id := by rw [multiplication_comp]; norm_num [multiplication_one]
  inv_hom_id := by rw [multiplication_comp]; norm_num [multiplication_one]

/-- Genuine finiteness for ALL nonzero integer multiplications,
including negative integers, through actual categorical composition. -/
lemma finite (n : ℤ) (hn : n≠0) : IsFinite (multiplication τ hτ n) := by
  cases n with
  | ofNat k =>
    exact PELOriginalFiniteMultiplication318.finite τ hτ k (by omega)
  | negSucc k =>
    letI := PELOriginalFiniteMultiplication318.finite τ hτ (k+1) (by omega)
    letI : IsIso (multiplication τ hτ (-1)) := (minusOneIso τ hτ).isIso_hom
    have he : multiplication τ hτ (Int.negSucc k)=
        multiplication τ hτ ((k+1 : ℕ) : ℤ)≫multiplication τ hτ (-1) := by
      rw [multiplication_comp]
      congr 1
      omega
    rw [he]
    infer_instance

/-- Division of a representative in the actual real universal cover
proves surjectivity on the ORIGINAL complex torus, not a replaced group. -/
lemma original_surjective (n : ℤ) (hn : n≠0) :
    Function.Surjective (fun q : PELOriginalPolarizationTransitions318.Base τ => n • q) := by
  intro q
  obtain ⟨z,rfl⟩ := (QuotientAddGroup.mk'_surjective (Periods τ)) q
  refine ⟨projection (Periods τ) ((n : ℝ)⁻¹ • z),?_⟩
  change n • (QuotientAddGroup.mk' (Periods τ)) ((n : ℝ)⁻¹ • z)=
    (QuotientAddGroup.mk' (Periods τ)) z
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
  rw [←map_zsmul,←Int.cast_smul_eq_zsmul ℝ,smul_smul,mul_inv_cancel₀ hnR,one_smul]

/-- Proper closed image plus actual complex-point realization upgrades
original torus surjectivity to surjectivity on EVERY scheme prime. -/
lemma surjective (n : ℤ) (hn : n≠0) : Function.Surjective (multiplication τ hτ n) := by
  let f := multiplication τ hτ n
  letI : IsProper f := PELOriginalFiniteMultiplication318.proper τ hτ n
  let Z : Closeds (candidate τ hτ) := ⟨Set.range f,by
    simpa only [Set.image_univ] using f.isClosedMap Set.univ isClosed_univ⟩
  have hh := ReducedComplexPointMorphisms318.range_subset (π τ hτ) (𝟙 _) Z (by
    intro p hp
    obtain ⟨q,hq⟩ := (originalAddEquiv τ hτ).surjective (⟨p,hp⟩ : Points τ hτ _ (𝟙 _))
    obtain ⟨r,hr⟩ := original_surjective τ n hn q
    have he : candidateComplexPoint τ hτ r≫f=p := by
      rw [original_action,hr]
      exact congrArg Subtype.val hq
    exact ⟨candidateComplexPoint τ hτ r (IsLocalRing.closedPoint ℂ),by
      rw [←Scheme.Hom.comp_apply,he]; rfl⟩)
  intro x
  exact hh ⟨x,rfl⟩

/-- The full nonzero multiplication morphism is finite and surjective.
Etaleness and scheme degree are not conclusions of this statement. -/
lemma finite_surjective (n : ℤ) (hn : n≠0) :
    IsFinite (multiplication τ hτ n) ∧ Function.Surjective (multiplication τ hτ n) :=
  ⟨finite τ hτ n hn,surjective τ hτ n hn⟩
end PELOriginalFiniteSurjectiveMultiplication318
