module
public import OriginalCartesianCurveReconstruction318
public import OriginalProjectiveBaseIntegral318
public section
noncomputable section
namespace OriginalIntegralBaseReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p] [IsIntegralHom p]
include p in
/-- The integral original quotient constructs this exact base instance; it is
not registered as an instance whose source morphism cannot be inferred. -/
lemma baseIntegral : IsIntegral (ProjectiveJLine318.scheme ℚ) :=
  OriginalProjectiveBaseIntegral318.integral p
variable
  (b : ArithmeticGroup → (Y ≅ Y))
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
  (hfixed : letI := baseIntegral p
    ∀ x : Y.functionField,
    (∀ w, OriginalSchemeDeckFieldAction318.ringEquiv b w x = x) →
      ∃ r : RatFunc ℚ, (DominantFunctionField318.map p).hom (OriginalProjectiveFunctionCoordinate318.κ r) = x)

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (f : Polynomial ℚ →+* A)
  (H : IsPullback (Spec.map (CommRingCat.ofHom f)) j (JLineAtlas318.chart ℚ 1) p)

variable
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include bone bmul hover hb hfixed H hcover hnormal in
/-- The actual original integral quotient supplies the integral projective
base instance too. All auxiliary field, coordinate, scalar, normal-chart and
generic compatibility inputs are now constructed from the old geometry. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalCartesianCurveReconstruction318.BranchLocus b j f l m) :
    letI := baseIntegral p
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
  letI := baseIntegral p
  letI : Algebra (RatFunc ℚ) Y.functionField :=
    OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ
  letI : FiniteDimensional (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1
  letI : IsGalois (RatFunc ℚ) Y.functionField :=
    (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1
  exact OriginalCartesianCurveReconstruction318.original_curve p b bone bmul hover hb hfixed
    j f H V hcover hnormal l m hmodels hbranch
end OriginalIntegralBaseReconstruction318
