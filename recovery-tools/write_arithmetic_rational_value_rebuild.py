from pathlib import Path
import shutil,json
root=Path(__file__).resolve().parents[1];b=root/'quartics/quartic-318-326/proof/experiments';old=b/'forward-actual-two-descent-original-local-fractional-sheaf-rebuild-r1';p=b/'forward-actual-two-descent-original-rational-value-rebuild-r1'
if not p.exists():shutil.copytree(old,p)
sources={}
sources['ActualTwoDescentOpenRationalEvaluationRebuild318']='''module
public import ActualTwoDescentOriginalInfinityFractionalSheafRebuild318
public import OpenFunctionField318
public section
noncomputable section
namespace ActualTwoDescentOpenRationalEvaluationRebuild318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : Y ⟶ X) [IsOpenImmersion j]

/-- Every nonempty ambient open meets the actual integral open chart. -/
lemma preimage_nonempty (U : X.Opens) [Nonempty U] : Nonempty (j ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint Y,?_⟩⟩
  change j (genericPoint Y) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion j]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

local instance (U : X.Opens) [Nonempty U] : Nonempty (j ⁻¹ᵁ U) := preimage_nonempty j U

/-- Actual section germ followed by the inverse ACTUAL open-chart stalk map. -/
def evaluation (U : X.Opens) [Nonempty U] : Γ(Y,j ⁻¹ᵁ U) →+* X.functionField :=
  (OpenFunctionField318.fieldEquiv j).symm.toRingHom.comp
    (Y.germToFunctionField (j ⁻¹ᵁ U)).hom

lemma injective (U : X.Opens) [Nonempty U] : Function.Injective (evaluation j U) :=
  (OpenFunctionField318.fieldEquiv j).symm.injective.comp
    (Y.germToFunctionField_injective (j ⁻¹ᵁ U))

lemma ambient (U : X.Opens) [Nonempty U] (a : Γ(X,U)) :
    evaluation j U (j.app U a)=X.germToFunctionField U a := by
  apply (OpenFunctionField318.fieldEquiv j).injective
  have h := congrArg (fun k => k a) (OpenFunctionField318.fieldIso_germ j U)
  change OpenFunctionField318.fieldEquiv j (X.germToFunctionField U a)=
    Y.germToFunctionField (j ⁻¹ᵁ U) (j.app U a) at h
  change OpenFunctionField318.fieldEquiv j
    ((OpenFunctionField318.fieldEquiv j).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  exact h.symm

lemma restrict (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (a : Γ(Y,j ⁻¹ᵁ U)) :
    evaluation j V (Y.presheaf.map (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from
      fun x hx => h hx)).op a)=evaluation j U a := by
  apply congrArg (OpenFunctionField318.fieldEquiv j).symm
  exact Y.presheaf.germ_res_apply (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from
    fun x hx => h hx)) (genericPoint Y) _ a
end ActualTwoDescentOpenRationalEvaluationRebuild318
'''
sources['ActualTwoDescentPushforwardRationalValueRebuild318']='''module
public import ActualTwoDescentOpenRationalEvaluationRebuild318
public section
noncomputable section
namespace ActualTwoDescentPushforwardRationalValueRebuild318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
  (f : M ⟶ (Scheme.Modules.pushforward j).obj (ClutchedModule318.unit Y))

/-- A genuine all-nonempty-open rational value, from a specified native
pushforward morphism. This definition alone does not assert injectivity. -/
def value (U : X.Opens) [Nonempty U] (s : Γ(M,U)) : X.functionField :=
  ActualTwoDescentOpenRationalEvaluationRebuild318.evaluation j U (f.app U s)

lemma add (U : X.Opens) [Nonempty U] (s t : Γ(M,U)) :
    value j M f U (s+t)=value j M f U s+value j M f U t := by
  simp only [value,map_add]

lemma scalar (U : X.Opens) [Nonempty U] (a : Γ(X,U)) (s : Γ(M,U)) :
    value j M f U (a • s)=X.germToFunctionField U a*value j M f U s := by
  have hs := Scheme.Modules.Hom.app_smul f a s
  change f.app U (a • s)=j.app U a*f.app U s at hs
  unfold value
  rw [hs,map_mul,ActualTwoDescentOpenRationalEvaluationRebuild318.ambient]

lemma restrict (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(M,U)) :
    value j M f V (M.presheaf.map (homOfLE h).op s)=value j M f U s := by
  have hn := PresheafOfModules.naturality_apply f.val (homOfLE h).op s
  change f.app V (M.presheaf.map (homOfLE h).op s)=
    Y.presheaf.map (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from fun x hx => h hx)).op
      (f.app U s) at hn
  unfold value
  rw [hn]
  exact ActualTwoDescentOpenRationalEvaluationRebuild318.restrict j U V h _

lemma eq_iff (U : X.Opens) [Nonempty U] (s t : Γ(M,U)) :
    value j M f U s=value j M f U t ↔ f.app U s=f.app U t :=
  (ActualTwoDescentOpenRationalEvaluationRebuild318.injective j U).eq_iff
end ActualTwoDescentPushforwardRationalValueRebuild318
'''
sources['ActualTwoDescentOriginalGlobalRationalValueRebuild318']='''module
public import ActualTwoDescentPushforwardRationalValueRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalGlobalRationalValueRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- The old affine projection and literal ideal inclusion, restricted
through the COMPLETE actual overlap. No new gluing hypothesis is supplied. -/
def coefficientMap (n : K) (i : Fin 3) : originalRootIdealSheaf n i ⟶
    (Scheme.Modules.pushforward (overlapEmbedding n)).obj
      (ClutchedModule318.unit (overlapScheme n)) :=
  affineProjection n i ≫ affineIdealRestriction n i

lemma infinity_coefficientMap (n : K) (i : Fin 3) : coefficientMap n i=
    infinityProjection n i ≫ infinityInverseRestriction n :=
  actual_ideal_sheaf_compatibility n i

/-- Every nonempty ambient section now has a canonical value in the SAME
original generic field. Injectivity/global image is not asserted here. -/
def value (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U]
    (s : Γ(originalRootIdealSheaf n i,U)) : (originalCubicScheme n).functionField :=
  ActualTwoDescentPushforwardRationalValueRebuild318.value (overlapEmbedding n)
    (originalRootIdealSheaf n i) (coefficientMap n i) U s

lemma infinity_formula (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (s : Γ(originalRootIdealSheaf n i,U)) : value n i U s=
    ActualTwoDescentOpenRationalEvaluationRebuild318.evaluation (overlapEmbedding n) U
      ((infinityInverseRestriction n).app U ((infinityProjection n i).app U s)) := by
  unfold value ActualTwoDescentPushforwardRationalValueRebuild318.value
  rw [infinity_coefficientMap] <;> rfl

lemma restrict (n : K) (i : Fin 3) (U V : (originalCubicScheme n).Opens)
    [Nonempty U] [Nonempty V] (h : V ≤ U) (s : Γ(originalRootIdealSheaf n i,U)) :
    value n i V ((originalRootIdealSheaf n i).presheaf.map (homOfLE h).op s)=value n i U s :=
  ActualTwoDescentPushforwardRationalValueRebuild318.restrict _ _ _ U V h s

lemma scalar (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (a : Γ(originalCubicScheme n,U)) (s : Γ(originalRootIdealSheaf n i,U)) :
    value n i U (a • s)=(originalCubicScheme n).germToFunctionField U a*value n i U s :=
  ActualTwoDescentPushforwardRationalValueRebuild318.scalar _ _ _ U a s
end ActualTwoDescentOriginalGlobalRationalValueRebuild318
'''
sources['ActualTwoDescentOriginalOverlapRationalFrameRebuild318']='''module
public import ActualTwoDescentOriginalGlobalRationalValueRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapRationalFrameRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
open ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

/-- Exact local frame value in the original field on EVERY nonempty
subopen of the literal common chart. -/
def value (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (s : Γ(overlapIdeal n i,U)) : (originalCubicScheme n).functionField :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
    ((overlapScheme n).germToFunctionField U ((affineValue n i).app U s))

lemma injective (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U] :
    Function.Injective (value n i U) := by
  letI := actual_affine_value_isIso n i
  have hb := (ConcreteCategory.isIso_iff_bijective ((affineValue n i).app U)).mp
    (inferInstance : IsIso ((affineValue n i).app U))
  exact (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.injective.comp
    (((overlapScheme n).germToFunctionField_injective U).comp hb.injective)

/-- Full actual inverse-u transition, with the restricted section and
native field map retained. Not just equality at a chosen point. -/
lemma infinity_formula (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (s : Γ(overlapIdeal n i,U)) : value n i U s=
    (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
      ((overlapScheme n).germToFunctionField U ((infinityValue n i).app U s)) *
    (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
      ((overlapScheme n).germToFunctionField U
        ((overlapScheme n).presheaf.map (homOfLE (show U≤⊤ from le_top)).op
          (inverseUSection n))) := by
  unfold value
  rw [actual_overlap_values_apply,map_mul,map_mul]

lemma adjoint (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _
      (affineValue n i)=ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i :=
  Equiv.apply_symm_apply _ _
end ActualTwoDescentOriginalOverlapRationalFrameRebuild318
'''
for n,s in sources.items():(p/(n+'.lean')).write_text(s)
print(p,len(sources),sum(len(s.splitlines()) for s in sources.values()))
