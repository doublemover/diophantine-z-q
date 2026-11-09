module
public import OriginalGeometricBranchLocus318
public section
noncomputable section
namespace OriginalCurveGeometricStabilizers318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]
  {Y : Scheme}
  (j : Spec (CommRingCat.of (Order L)) ⟶ Y) [Mono j]
  (a : Group L → (Y ⟶ Y))
  (hj : ∀ σ, schemeMap L σ ≫ j = j ≫ a σ)

@[expose] def point {F : Type} [Field F] (p : Order L →+* F) :
    Spec (CommRingCat.of F) ⟶ Y := NormalClosureGeometricPoints318.point L p ≫ j

include hj in
/-- Exact chart cancellation retains the ORIGINAL whole-curve maps and
literal geometric point. It is not equality of topological point supports. -/
lemma fixed_iff {F : Type} [Field F] (p : Order L →+* F) (σ : Group L) :
    point j p ≫ a σ = point j p ↔
      NormalClosureGeometricPoints318.point L p ≫ schemeMap L σ =
        NormalClosureGeometricPoints318.point L p := by
  unfold point
  rw [Category.assoc, ← hj σ, ← Category.assoc]
  exact (cancel_mono j)

/-- Genuine stabilizer statement on original whole-curve geometric points
in its actual finite-coordinate chart. No inertia or valuation input remains. -/
@[expose] def PointBranchLocus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Order L →+* F),
    ((∀ k, coordinate L p ≠ contactValue L p k) ∧
      ∀ σ : Group L, point j p ≫ a σ = point j p ↔ σ = 1) ∨
    ∃ k : Fin 4, coordinate L p = contactValue L p k ∧
      ∀ σ : Group L, point j p ≫ a σ = point j p ↔
        σ = 1 ∨ labels σ = FourBinaryCharacters318.flip k

include hj in
/-- Convert the actual whole-curve stabilizer theorem into the original
full inertia branch locus, using the unchanged original chart square. -/
theorem full_inertia
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : PointBranchLocus j a labels) :
    OriginalFullInertiaReconstruction318.BranchLocus labels := by
  apply OriginalGeometricBranchLocus318.full_inertia labels
  intro F _ _ p
  rcases h F p with hu | ⟨k,hk,hs⟩
  · refine Or.inl ⟨hu.1,?_⟩
    intro σ
    exact (fixed_iff j a hj p σ).symm.trans (hu.2 σ)
  · refine Or.inr ⟨k,hk,?_⟩
    intro σ
    exact (fixed_iff j a hj p σ).symm.trans (hs σ)

variable [IsIntegral Y]
  (g : Spec (CommRingCat.of L) ⟶ Y) (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  [IsDominant g] [IsIntegralHom p] [IsIso (DominantFunctionField318.map g)]
  (hbase : g ≫ p = ReconstructedFieldNormalization318.base L)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hj in
/-- A connected geometric-point-to-original-curve reconstruction. The real
PEL curve, its normalized coordinate/chart and full labeled point stabilizer
theorem are still required; no historical assertion supplies them automatically. -/
theorem original_curve
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : PointBranchLocus j a labels) :
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
end OriginalCurveGeometricStabilizers318
