module
public import OriginalContactInertiaBasis318
public import OriginalPublishedComplexBranches318
public section
noncomputable section
namespace OriginalArithmeticBranchReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme} (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (a : Group L → (Y ⟶ Y))
  (hj : ∀ σ, schemeMap L σ ≫ j = j ≫ a σ)

/-- The labels now lie in the ORIGINAL arithmetic prime-squareclass group.
Identifying actual PEL deck/Galois maps with normalizer parity is still needed;
no equality of its kernel with the analytic coarse kernel is presumed. -/
@[expose] def BranchLocus
    (arithmeticLabels : Group L ≃* Multiplicative InertiaLabels318.V) (l m : ℂ) : Prop :=
  ∀ p : Order L →+* ℂ,
    ((∀ k, coordinate L p ≠ OriginalPublishedComplexBranches318.branchValues l m k) ∧
      ∀ σ : Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔ σ = 1) ∨
    ∃ k : Fin 4,
      coordinate L p = OriginalPublishedComplexBranches318.branchValues l m k ∧
      ∀ σ : Group L, OriginalCurveGeometricStabilizers318.point j p ≫ a σ =
        OriginalCurveGeometricStabilizers318.point j p ↔
          σ = 1 ∨ arithmeticLabels σ = Multiplicative.ofAdd
            (InertiaLabels318.labels (OriginalContactInertiaBasis318.reverse k))

/-- The exact original arithmetic labels yield the four literal root flips.
The explicit inverse matrix and row reversal prevent a silent label swap. -/
theorem contact_branch_locus
    (arithmeticLabels : Group L ≃* Multiplicative InertiaLabels318.V) (l m : ℂ)
    (h : BranchLocus j a arithmeticLabels l m) :
    OriginalPublishedComplexBranches318.BranchLocus j a
      (arithmeticLabels.trans OriginalContactInertiaBasis318.basis) l m := by
  intro p
  have hp := h p
  simpa only [MulEquiv.trans_apply,OriginalContactInertiaBasis318.finite_iff] using hp

variable [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hj hbase hcover hnormal in
/-- The actual arithmetic-label-to-original-curve endpoint retains the SAME
original generic automorphisms and explicitly computes their root-sign basis.
No PEL algebraization, full branch law or normalizer-kernel equality is inferred. -/
theorem original_curve
    (arithmeticLabels : Group L ≃* Multiplicative InertiaLabels318.V) (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : BranchLocus j a arithmeticLabels l m) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] L,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          g ≫ E.hom = (ReconstructedFieldNormalization318.specIso L c e).hom ≫
            ContactFieldNormalization318.genericSource c ∧
          ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
            (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
              (FourBinaryCharacters318.signPattern
                (OriginalContactInertiaBasis318.basis (arithmeticLabels σ))) z) :=
  OriginalPublishedComplexBranches318.original_curve j a hj g p hbase V hcover hnormal
    (arithmeticLabels.trans OriginalContactInertiaBasis318.basis) l m hmodels
    (contact_branch_locus j a arithmeticLabels l m hbranch)
end OriginalArithmeticBranchReconstruction318
