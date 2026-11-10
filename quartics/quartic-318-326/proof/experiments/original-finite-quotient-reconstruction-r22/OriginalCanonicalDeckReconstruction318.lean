module
public import OriginalNormalClosureChartAction318
public import OriginalSchemeDeckFieldAction318
public import OriginalActualDeckEquivariance318
public section
noncomputable section
namespace OriginalCanonicalDeckReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  [IsIntegral (ProjectiveJLine318.scheme ℚ)]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p] [IsIntegralHom p]
  (κ : RatFunc ℚ →+* (ProjectiveJLine318.scheme ℚ).functionField)
  (b : ArithmeticGroup → (Y ≅ Y))
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
  (hfixed : ∀ x : Y.functionField,
    (∀ w, OriginalSchemeDeckFieldAction318.ringEquiv b w x = x) →
      ∃ r : RatFunc ℚ, (DominantFunctionField318.map p).hom (κ r) = x)

local instance actualBase : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p κ

local instance actualFinite : FiniteDimensional (RatFunc ℚ) Y.functionField :=
  (OriginalSchemeDeckFieldAction318.field_structure p κ b bone bmul hover hb hfixed).1

local instance actualGalois : IsGalois (RatFunc ℚ) Y.functionField :=
  (OriginalSchemeDeckFieldAction318.field_structure p κ b bone bmul hover hb hfixed).2.1

local instance genericBirational :
    IsIso (DominantFunctionField318.map (OriginalGenericStalkNaturality318.generic Y)) :=
  OriginalGenericStalkNaturality318.generic_functionField_isIso (X := Y)

variable (j : Spec (CommRingCat.of (Order Y.functionField)) ⟶ Y) [Mono j]
  (hj : OriginalNormalClosureChartAction318.fraction Y.functionField ≫ j =
    OriginalGenericStalkNaturality318.generic Y)
  (hp : j ≫ p = OriginalNormalClosureChartAction318.chartBase Y.functionField)
  {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

include bone bmul hover hb hfixed hj hp hcover hnormal in
/-- The canonical original scheme maps now feed the complete reconstruction:
no separate generic embedding, birationality, field representation,
field-faithfulness, finite/Galois/degree hypothesis, generic action square,
or whole-chart action square is supplied. Genuine original algebraic curve,
normal chart/base squares, quotient fixed functions and branch/model laws
remain required. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalDeckCurveReconstruction318.BranchLocus j (fun w => (b w).hom) l m) :
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
  let ρ := OriginalSchemeDeckFieldAction318.representation p κ b bone bmul hover
  have hρ : Function.Injective ρ :=
    OriginalSchemeDeckFieldAction318.representation_injective p κ b bone bmul hover hb
  have hf : ∀ x : Y.functionField, (∀ w, ρ w x = x) →
      ∃ r : RatFunc ℚ, algebraMap (RatFunc ℚ) Y.functionField r = x := hfixed
  have hgeneric : ∀ w, OriginalGenericStalkNaturality318.generic Y ≫ (b w).hom =
      Spec.map (CommRingCat.ofHom (ρ w).toRingHom) ≫
        OriginalGenericStalkNaturality318.generic Y :=
    OriginalSchemeDeckFieldAction318.generic_square p κ b bone bmul hover
  have hchart : ∀ w, NormalClosureGeometricPoints318.schemeMap Y.functionField (ρ w) ≫ j =
      j ≫ (b w).hom := fun w =>
    OriginalNormalClosureChartAction318.chart_action j
      (OriginalGenericStalkNaturality318.generic Y) p hj hp (ρ w) (b w).hom
      (hover w) (hgeneric w)
  have hbase : OriginalGenericStalkNaturality318.generic Y ≫ p =
      ReconstructedFieldNormalization318.base Y.functionField :=
    OriginalNormalClosureChartAction318.generic_base j
      (OriginalGenericStalkNaturality318.generic Y) p hj hp
  exact OriginalActualDeckEquivariance318.original_curve ρ hρ hf j (fun w => (b w).hom)
    hchart (OriginalGenericStalkNaturality318.generic Y) p hbase V hcover hnormal
    hover hgeneric l m hmodels hbranch
end OriginalCanonicalDeckReconstruction318
