module
public import OriginalClosedResiduePoints318
public import OriginalCurveGeometricStabilizers318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace OriginalComplexPointReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme} (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (a : OriginalNormalClosureGalois318.Group L → (Y ⟶ Y))
  (hj : ∀ σ, schemeMap L σ ≫ j = j ≫ a σ)

/-- Only literal COMPLEX points of the actual original curve are tested.
The coordinate, affine chart and whole-curve automorphisms are unchanged. -/
@[expose] def ComplexBranchLocus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group) : Prop :=
  ∀ p : Order L →+* ℂ,
    ((∀ k, coordinate L p ≠ contactValue L p k) ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔ σ = 1) ∨
    ∃ k : Fin 4, coordinate L p = contactValue L p k ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔
          σ = 1 ∨ labels σ = FourBinaryCharacters318.flip k

include hj in
/-- Complex stabilizers suffice for the entire original arithmetic inertia
locus: every closed-prime residue embeds into C by its proved finite extension
of Q. No rationality assumption on the prime is introduced. -/
theorem full_inertia
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : ComplexBranchLocus j a labels) :
    OriginalFullInertiaReconstruction318.BranchLocus labels := by
  intro q hq P hP hc
  letI := hP
  obtain ⟨p,hker⟩ := OriginalClosedResiduePoints318.exists_point L ℂ q hq P hc
  have hs (σ : OriginalNormalClosureGalois318.Group L) : OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
      OriginalCurveGeometricStabilizers318.point j p ↔ σ ∈ P.inertia (OriginalNormalClosureGalois318.Group L) :=
    (OriginalCurveGeometricStabilizers318.fixed_iff j a hj p σ).trans
      (scheme_fixed_iff p P hker σ)
  rcases h p with hu | ⟨k,hk,hfix⟩
  · refine Or.inl ⟨?_,?_⟩
    · intro σ
      exact (hs σ).symm.trans (hu.2 σ)
    · intro k he
      exact hu.1 k ((contact_iff p P hker q hq hc k).mp he)
  · refine Or.inr ⟨k,(contact_iff p P hker q hq hc k).mpr hk,?_⟩
    intro σ
    exact (hs σ).symm.trans (hfix σ)

variable [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hj hbase hcover hnormal in
/-- The SAME algebraic candidate curve is reconstructed from its actual
complex point stabilizers and normalized coordinate. Constructing that PEL
curve and its complete complex branch law remains a genuine geometric input. -/
theorem original_curve
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : ComplexBranchLocus j a labels) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern (labels σ)) z) :=
  OriginalFullInertiaReconstruction318.original_curve_of_branch_locus
    g p hbase V hcover hnormal labels (full_inertia j a hj labels h)
end OriginalComplexPointReconstruction318
