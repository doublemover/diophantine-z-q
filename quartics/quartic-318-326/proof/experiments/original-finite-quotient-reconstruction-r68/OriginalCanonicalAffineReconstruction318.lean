module
public import OriginalCanonicalAffineChart318
public section
noncomputable section
namespace OriginalCanonicalAffineReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p] [IsIntegralHom p]
include p in
/-- The original quotient supplies its integral base explicitly. -/
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

variable
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include hcover hnormal in
/-- The original full normal cover supplies this exact section-ring instance. -/
lemma canonicalNormal : IsIntegrallyClosed (OriginalCanonicalAffineChart318.Ring p) :=
  OriginalCanonicalAffineChart318.ring_normal p V hcover hnormal

include bone bmul hover hb hfixed hcover hnormal in
/-- The entire normal Cartesian finite chart is now constructed from the
original quotient and original normal cover. No affine ring, embedding,
coefficient map, scalar tower or Cartesian square is supplied separately. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalCartesianCurveReconstruction318.BranchLocus b
      (OriginalCanonicalAffineChart318.chart p) (OriginalCanonicalAffineChart318.coefficient p) l m) :
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
  letI : IsIntegrallyClosed (OriginalCanonicalAffineChart318.Ring p) :=
    canonicalNormal p V hcover hnormal
  exact OriginalIntegralBaseReconstruction318.original_curve p b bone bmul hover hb hfixed
    (OriginalCanonicalAffineChart318.chart p) (OriginalCanonicalAffineChart318.coefficient p)
    (OriginalCanonicalAffineChart318.square p) V hcover hnormal l m hmodels hbranch
end OriginalCanonicalAffineReconstruction318
