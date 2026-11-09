module
public import OriginalAffineSectionReconstruction318
public import OriginalCanonicalQuotientBase318
public section
noncomputable section
namespace OriginalCanonicalCoordinateReconstruction318
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

local instance actualBase : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ

local instance actualFinite : FiniteDimensional (RatFunc ℚ) Y.functionField :=
  (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).1

local instance actualGalois : IsGalois (RatFunc ℚ) Y.functionField :=
  (OriginalSchemeDeckFieldAction318.field_structure p OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed).2.1

variable (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
  [Algebra (Polynomial ℚ) Γ(Y,U)]
  [IsScalarTower (Polynomial ℚ) Γ(Y,U) Y.functionField]
  [IsIntegrallyClosed Γ(Y,U)] [Algebra.IsIntegral (Polynomial ℚ) Γ(Y,U)]
  (hbase : hU.fromSpec ≫ p =
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) Γ(Y,U))) ≫ JLineAtlas318.chart ℚ 1)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include bone bmul hover hb hfixed hbase in
/-- The quotient coordinate is now canonical, built from the original
standard projective t-chart. The same quotient map proves its generic/base
square, and actual normal affine sections supply the old curve chart. No
independent rational-function coordinate or generic/base map is supplied. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalDeckCurveReconstruction318.BranchLocus
      (OriginalNormalAffineChart318.chart U hU) (fun w => (b w).hom) l m) :
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
  refine ⟨OriginalCanonicalQuotientBase318.generic_base p, ?_⟩
  exact OriginalAffineSectionReconstruction318.original_curve p
    OriginalProjectiveFunctionCoordinate318.κ b bone bmul hover hb hfixed U hU hbase
    V hcover hnormal l m hmodels hbranch
end OriginalCanonicalCoordinateReconstruction318
