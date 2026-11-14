module
public import OriginalCartesianNormalChart318
public import OriginalCanonicalDeckReconstruction318
public section
noncomputable section
namespace OriginalCartesianCurveReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  [IsIntegral (ProjectiveJLine318.scheme ℚ)]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p] [IsIntegralHom p]
  (b : ArithmeticGroup → (Y ≅ Y))
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
  (hfixed : ∀ x : Y.functionField,
    (∀ w, OriginalSchemeDeckFieldAction318.ringEquiv b w x = x) →
      ∃ r : RatFunc ℚ, (DominantFunctionField318.map p).hom (OriginalProjectiveFunctionCoordinate318.κ r) = x)

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (f : Polynomial ℚ →+* A)
  (H : IsPullback (Spec.map (CommRingCat.ofHom f)) j (JLineAtlas318.chart ℚ 1) p)

@[expose] def point (q : A →+* ℂ) : Spec (CommRingCat.of ℂ) ⟶ Y :=
  Spec.map (CommRingCat.ofHom q) ≫ j

/-- The complete branch law is stated on the ACTUAL original Cartesian
chart and its original coordinate f(X), not on a replacement closure ring. -/
@[expose] def BranchLocus (l m : ℂ) : Prop :=
  ∀ q : A →+* ℂ,
    ((∀ k, q (f Polynomial.X) ≠ OriginalPublishedComplexBranches318.branchValues l m k) ∧
      ∀ w : ArithmeticGroup, point j q ≫ (b w).hom = point j q ↔ w = 1) ∨
    ∃ k : Fin 4,
      q (f Polynomial.X) = OriginalPublishedComplexBranches318.branchValues l m k ∧
      ∀ w : ArithmeticGroup, point j q ≫ (b w).hom = point j q ↔
        w = 1 ∨ w = Multiplicative.ofAdd
          (InertiaLabels318.labels (OriginalContactInertiaBasis318.reverse k))

include bone bmul hover hb hfixed H in
lemma closure_branch (l m : ℂ) (h : BranchLocus b j f l m) :
    letI : Algebra (RatFunc ℚ) Y.functionField :=
      OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField :=
      (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1
    letI : IsGalois (RatFunc ℚ) Y.functionField :=
      (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1
    OriginalDeckCurveReconstruction318.BranchLocus
      (OriginalCartesianNormalChart318.chart p j f H) (fun w => (b w).hom) l m := by
  letI : Algebra (RatFunc ℚ) Y.functionField :=
    OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1
  letI : IsGalois (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1
  intro z
  have hz := h (z.comp (OriginalCartesianNormalChart318.sections p j f H).toRingHom)
  dsimp only [point] at hz
  rw [← OriginalCartesianNormalChart318.point_chart p j f H z] at hz
  simpa only [OriginalCartesianNormalChart318.point_coefficient,
    NormalClosureGeometricPoints318.coordinate] using hz

variable
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include bone bmul hover hb hfixed H hcover hnormal in
/-- Actual Cartesian affine geometry derives the coefficient algebra,
scalar tower and integrality needed for original normal-closure reconstruction.
Only the actual normal affine ring/chart and full old branch law remain; no
additional compatibility of field and affine coefficients is supplied. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : BranchLocus b j f l m) :
    letI : Algebra (RatFunc ℚ) Y.functionField :=
      OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
    letI : FiniteDimensional (RatFunc ℚ) Y.functionField :=
      (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1
    letI : IsGalois (RatFunc ℚ) Y.functionField :=
      (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1
    (OriginalGenericStalkNaturality318.generic Y ≫ p =
      ReconstructedFieldNormalization318.base Y.functionField) ∧
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : ContactFieldNormalization318.Field c ≃ₐ[RatFunc ℚ] Y.functionField,
        ∃ E : Y ≅ ContactProjectiveModel318.model c,
          E.hom ≫ ContactProjectiveModel318.modelMap c = p ∧
          OriginalGenericStalkNaturality318.generic Y ≫ E.hom =
            (ReconstructedFieldNormalization318.specIso Y.functionField c e).hom ≫
              ContactFieldNormalization318.genericSource c ∧
          (∀ (w : ArithmeticGroup) z,
            OriginalSchemeDeckFieldAction318.ringEquiv b w (e z) = e
              (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
                (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) z)) ∧
          ∀ w : ArithmeticGroup, (b w).hom ≫ E.hom = E.hom ≫ ContactGlobalSigns318.map c
            (FourBinaryCharacters318.signPattern (OriginalContactInertiaBasis318.basis w)) := by
  letI : Algebra (RatFunc ℚ) Y.functionField :=
    OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1
  letI : IsGalois (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1
  refine ⟨OriginalCanonicalQuotientBase318.generic_base p, ?_⟩
  exact OriginalCanonicalDeckReconstruction318.original_curve p
    OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed
    (OriginalCartesianNormalChart318.chart p j f H)
    (OriginalCartesianNormalChart318.fraction_chart p j f H)
    (OriginalCartesianNormalChart318.chart_base p j f H)
    V hcover hnormal l m hmodels
    (closure_branch p b bone bmul hover hb hfixed j f H l m hbranch)
end OriginalCartesianCurveReconstruction318
