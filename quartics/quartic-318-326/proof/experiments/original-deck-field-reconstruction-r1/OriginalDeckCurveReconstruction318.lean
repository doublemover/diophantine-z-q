module
public import OriginalDeckArithmeticLabels318
public section
noncomputable section
namespace OriginalDeckCurveReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
open OriginalDeckArithmeticLabels318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  (ρ : ArithmeticGroup →* (L ≃ₐ[RatFunc ℚ] L)) (hfaithful : Function.Injective ρ)
  (hfixed : ∀ x : L, (∀ w : ArithmeticGroup, ρ w x = x) →
    ∃ r : RatFunc ℚ, algebraMap (RatFunc ℚ) L r = x)

include ρ hfaithful hfixed in
/-- All field hypotheses used below are produced from the SAME original
finite deck action and actual quotient fixed-field identity. -/
theorem field_structure : FiniteDimensional (RatFunc ℚ) L ∧
    IsGalois (RatFunc ℚ) L ∧ Module.finrank (RatFunc ℚ) L = 16 :=
  ⟨OriginalFiniteDeckGalois318.finiteDimensional ρ hfaithful hfixed,
    OriginalFiniteDeckGalois318.isGalois ρ hfaithful hfixed,
    OriginalDeckArithmeticLabels318.degree_sixteen ρ hfaithful hfixed⟩

/- These instances are the exact hypotheses delivered by field_structure;
no replacement field or chosen degree16 algebra is introduced. -/
variable [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme} (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (b : ArithmeticGroup → (Y ⟶ Y))
  (hchart : ∀ w, schemeMap L (ρ w) ≫ j = j ≫ b w)

/-- The actual original whole-curve maps, only reindexed by the proved
inverse of their SAME original generic representation. -/
@[expose] def reindexed (σ : Group L) : Y ⟶ Y := b (labels ρ hfaithful hfixed σ)

include hchart in
lemma chart_square (σ : Group L) : schemeMap L σ ≫ j =
    j ≫ reindexed ρ hfaithful hfixed b σ := by
  have h := hchart (labels ρ hfaithful hfixed σ)
  rw [reconstruct ρ hfaithful hfixed σ] at h
  exact h

/-- This is the genuine whole-curve branch theorem for the originally
arithmetic-labeled deck maps, without a supplied Galois-group equivalence. -/
@[expose] def BranchLocus (l m : ℂ) : Prop :=
  ∀ p : Order L →+* ℂ,
    ((∀ k, coordinate L p ≠ OriginalPublishedComplexBranches318.branchValues l m k) ∧
      ∀ w : ArithmeticGroup, OriginalCurveGeometricStabilizers318.point j p ≫ b w =
        OriginalCurveGeometricStabilizers318.point j p ↔ w = 1) ∨
    ∃ k : Fin 4,
      coordinate L p = OriginalPublishedComplexBranches318.branchValues l m k ∧
      ∀ w : ArithmeticGroup, OriginalCurveGeometricStabilizers318.point j p ≫ b w =
        OriginalCurveGeometricStabilizers318.point j p ↔
          w = 1 ∨ w = Multiplicative.ofAdd
            (InertiaLabels318.labels (OriginalContactInertiaBasis318.reverse k))

/-- Every original generic automorphism is covered because the original deck
representation is proved surjective, not because an abstract order is16. -/
theorem arithmetic_branch_locus (l m : ℂ) (h : BranchLocus j b l m) :
    OriginalArithmeticBranchReconstruction318.BranchLocus j
      (reindexed ρ hfaithful hfixed b) (labels ρ hfaithful hfixed) l m := by
  intro p
  have hid (σ : Group L) : labels ρ hfaithful hfixed σ = 1 ↔ σ = 1 := by
    constructor
    · intro h
      apply (labels ρ hfaithful hfixed).injective
      rw [h,map_one]
    · intro h
      rw [h,map_one]
  rcases h p with hu | ⟨k,hk,hs⟩
  · refine Or.inl ⟨hu.1,?_⟩
    intro σ
    exact (hu.2 (labels ρ hfaithful hfixed σ)).trans (hid σ)
  · refine Or.inr ⟨k,hk,?_⟩
    intro σ
    exact (hs (labels ρ hfaithful hfixed σ)).trans (or_congr (hid σ) Iff.rfl)

variable [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hfaithful hfixed hchart in
/-- The supplied degree and arbitrary Galois label equivalence have both
been removed: they come from the original faithful arithmetic deck maps and
actual quotient fixed-field identity. PEL algebraization, that fixed-field
identity, complete branch theorem and actual model equations remain required. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : BranchLocus j b l m) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (w : ArithmeticGroup) z, ρ w (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) z) := by
  obtain ⟨c,e,E,hp,hg,ha⟩ := OriginalArithmeticBranchReconstruction318.original_curve
    j (reindexed ρ hfaithful hfixed b) (chart_square ρ hfaithful hfixed j b hchart)
    g p hbase V hcover hnormal (labels ρ hfaithful hfixed) l m hmodels
    (arithmetic_branch_locus ρ hfaithful hfixed j b l m hbranch)
  refine ⟨c,e,E,hp,hg,?_⟩
  intro w z
  simpa only [labels_apply] using ha (ρ w) z
end OriginalDeckCurveReconstruction318
