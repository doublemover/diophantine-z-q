module
public import OriginalFiniteProjectiveFlat318
public section
noncomputable section
namespace OriginalFinitePointReconstruction318
open AlgebraicGeometry CategoryTheory
open OriginalDeckArithmeticLabels318 OriginalNormalClosureGalois318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsFinite p] [IsDominant p]
  (b : ArithmeticGroup → (Y ≅ Y))
local instance originalFlat : Flat p := OriginalFiniteProjectiveFlat318.flat p
variable
  (bone : (b 1).hom = 𝟙 Y)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)
  (hb : Function.Injective (fun w => (b w).hom))
variable {ι : Type*} (V : ι → Y.affineOpens) (hcover : ⨆ i, (V i).1 = ⊤)
  (hnormal : ∀ i, IsIntegrallyClosed Γ(Y, (V i).1))

variable (y : Spec (CommRingCat.of ℂ) ⟶ ProjectiveJLine318.scheme ℚ)
  [Etale (OriginalUnramifiedFiberRank318.fiberMap p y)]
  (hcard : Nat.card (OriginalUnramifiedFiberRank318.OriginalPoints p y) = 16)

include bone bmul hover hb hcover hnormal hcard in
/-- Original finite dominant geometry supplies flatness, the actual
unramified sixteen-point fiber supplies degree and fixed functions, and
the original normal/branch/model data give the unchanged curve equivalence. -/
theorem original_curve (l m : ℂ)
    (hmodels : OriginalPublishedComplexBranches318.ModelInvariants l m)
    (hbranch : OriginalSchemeBranchReconstruction318.BranchLaw p b l m) :
    letI := OriginalQuotientRankFixed318.baseIntegral p
    letI := OriginalQuotientRankFixed318.actualBase p
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
  letI := OriginalQuotientRankFixed318.baseIntegral p
  letI := OriginalQuotientRankFixed318.actualBase p
  exact OriginalFiberPointReconstruction318.original_curve p b bone bmul hover hb
    V hcover hnormal y hcard l m hmodels hbranch
end OriginalFinitePointReconstruction318
