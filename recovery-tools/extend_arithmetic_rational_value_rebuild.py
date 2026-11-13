from pathlib import Path
p=Path('quartics/quartic-318-326/proof/experiments/forward-actual-two-descent-original-rational-value-rebuild-r1')
f=p/'ActualTwoDescentPushforwardRationalValueRebuild318.lean'
s=f.read_text().replace('have hs := (f.app U).hom.map_smul a s','have hs := Scheme.Modules.Hom.app_smul f a s')
f.write_text(s)
S={}
S['ActualTwoDescentOpenAdjointSectionsRebuild318']='''module
public import ActualTwoDescentOriginalOverlapRationalFrameRebuild318
public section
noncomputable section
namespace ActualTwoDescentOpenAdjointSectionsRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (M : X.Modules) (N : Y.Modules)

/-- The actual adjunction unit on every ambient open, not just top. -/
def restrictSection (U : X.Opens) (s : Γ(M,U)) : Γ(M.restrict j,j ⁻¹ᵁ U) :=
  ((Scheme.Modules.restrictAdjunction j).unit.app M).app U s

lemma section_formula (U : X.Opens) (s : Γ(M,U)) :
    restrictSection j M U s=M.presheaf.map (homOfLE (j.image_preimage_le U)).op s := rfl

/-- The whole native restriction/evaluation square for every section. -/
lemma adjoint_apply (e : M.restrict j ⟶ N) (U : X.Opens) (s : Γ(M,U)) :
    ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ e).app U s=
      e.app (j ⁻¹ᵁ U) (restrictSection j M U s) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma naturality (e : M ⟶ M) (U : X.Opens) (s : Γ(M,U)) :
    restrictSection j M U (e.app U s)=
      ((Scheme.Modules.restrictFunctor j).map e).app (j ⁻¹ᵁ U)
        (restrictSection j M U s) := by
  have h := (Scheme.Modules.restrictAdjunction j).unit.naturality e
  exact congrArg (fun q => q.app U s) h
end ActualTwoDescentOpenAdjointSectionsRebuild318
'''
S['ActualTwoDescentOriginalRationalRestrictionSquareRebuild318']='''module
public import ActualTwoDescentOpenAdjointSectionsRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- Restriction of the EXISTING global root ideal to the complete old overlap. -/
def restrictSection (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    (s : Γ(originalRootIdealSheaf n i,U)) : Γ(overlapIdeal n i,overlapEmbedding n ⁻¹ᵁ U) :=
  ActualTwoDescentOpenAdjointSectionsRebuild318.restrictSection (overlapEmbedding n)
    (originalRootIdealSheaf n i) U s

lemma coefficient_square (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    (s : Γ(originalRootIdealSheaf n i,U)) :
    (ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i).app U s=
      (affineValue n i).app (overlapEmbedding n ⁻¹ᵁ U) (restrictSection n i U s) := by
  rw [←ActualTwoDescentOriginalOverlapRationalFrameRebuild318.adjoint]
  exact ActualTwoDescentOpenAdjointSectionsRebuild318.adjoint_apply _ _ _ _ U s

/-- Exact global/local rational-value identification, over EVERY nonempty
ambient open. This was not implied by the separate existence of the maps. -/
lemma value_square (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
    ∀ s : Γ(originalRootIdealSheaf n i,U),
      ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=
        ActualTwoDescentOriginalOverlapRationalFrameRebuild318.value n i
          (overlapEmbedding n ⁻¹ᵁ U) (restrictSection n i U s) := by
  intro s
  change (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm
    ((overlapScheme n).germToFunctionField _
      ((ActualTwoDescentOriginalGlobalRationalValueRebuild318.coefficientMap n i).app U s))=_
  rw [coefficient_square]
  rfl

/-- Equality of rational values is EXACTLY equality of native restrictions.
Global injectivity requires injectivity of this native restriction. -/
lemma eq_iff_section (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (s t : Γ(originalRootIdealSheaf n i,U)) :
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=
      ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U t ↔
        restrictSection n i U s=restrictSection n i U t := by
  letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
  rw [value_square,value_square]
  exact (ActualTwoDescentOriginalOverlapRationalFrameRebuild318.injective n i _).eq_iff
end ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
'''
S['ActualTwoDescentOriginalRationalAdditiveImageRebuild318']='''module
public import ActualTwoDescentOriginalRationalRestrictionSquareRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalAdditiveImageRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalIdealOverlapValues318
variable {K : Type*} [Field K] [CharZero K]

/-- Genuine additive map into the same actual function field. -/
def valueHom (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U] :
    Γ(originalRootIdealSheaf n i,U) →+ (originalCubicScheme n).functionField where
  toFun := ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U
  map_zero' := by
    simp only [ActualTwoDescentOriginalGlobalRationalValueRebuild318.value,
      ActualTwoDescentPushforwardRationalValueRebuild318.value,map_zero]
  map_add' := ActualTwoDescentPushforwardRationalValueRebuild318.add _ _ _ U

def image (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U] :
    AddSubgroup (originalCubicScheme n).functionField := (valueHom n i U).range

lemma mem_image (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens) [Nonempty U]
    (z : (originalCubicScheme n).functionField) : z ∈ image n i U ↔
      ∃ s : Γ(originalRootIdealSheaf n i,U),
        ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U s=z := Iff.rfl

/-- Restrictions preserve actual rational values, hence give literal
inclusions of additive images, not a new field identification. -/
lemma antitone (n : K) (i : Fin 3) (U V : (originalCubicScheme n).Opens)
    [Nonempty U] [Nonempty V] (h : V≤U) : image n i U ≤ image n i V := by
  intro z hz
  obtain ⟨s,rfl⟩ := (mem_image n i U z).mp hz
  exact (mem_image n i V _).mpr ⟨(originalRootIdealSheaf n i).presheaf.map (homOfLE h).op s,
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.restrict n i U V h s⟩

lemma scalar_closed (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] (a : Γ(originalCubicScheme n,U)) (z : (originalCubicScheme n).functionField)
    (hz : z ∈ image n i U) :
    (originalCubicScheme n).germToFunctionField U a*z ∈ image n i U := by
  obtain ⟨s,rfl⟩ := (mem_image n i U z).mp hz
  exact (mem_image n i U _).mpr ⟨a • s,
    ActualTwoDescentOriginalGlobalRationalValueRebuild318.scalar n i U a s⟩
end ActualTwoDescentOriginalRationalAdditiveImageRebuild318
'''
S['ActualTwoDescentOriginalOverlapValueImageRebuild318']='''module
public import ActualTwoDescentOriginalRationalAdditiveImageRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapValueImageRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
variable {K : Type*} [Field K] [CharZero K]

/-- The full regular-function image on ANY nonempty common-chart open,
viewed in the original global field via the actual generic-stalk map. -/
def regularValue (n : K) (U : (overlapScheme n).Opens) [Nonempty U] :
    Γ(overlapScheme n,U) →+* (originalCubicScheme n).functionField :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.toRingHom.comp
    ((overlapScheme n).germToFunctionField U).hom

lemma regular_injective (n : K) (U : (overlapScheme n).Opens) [Nonempty U] :
    Function.Injective (regularValue n U) :=
  (OpenFunctionField318.fieldEquiv (overlapEmbedding n)).symm.injective.comp
    ((overlapScheme n).germToFunctionField_injective U)

/-- Entire image, proved using the old actual frame's surjectivity.
This is not generator agreement or a bare dimension argument. -/
lemma full_image (n : K) (i : Fin 3) (U : (overlapScheme n).Opens) [Nonempty U]
    (z : (originalCubicScheme n).functionField) :
    (∃ s : Γ(overlapIdeal n i,U),
      ActualTwoDescentOriginalOverlapRationalFrameRebuild318.value n i U s=z) ↔
    ∃ a : Γ(overlapScheme n,U),regularValue n U a=z := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(affineValue n i).app U s,rfl⟩
  · rintro ⟨a,ha⟩
    letI := actual_affine_value_isIso n i
    have hb := (ConcreteCategory.isIso_iff_bijective ((affineValue n i).app U)).mp
      (inferInstance : IsIso ((affineValue n i).app U))
    obtain ⟨s,hs⟩ := hb.surjective a
    refine ⟨s,?_⟩
    change regularValue n U ((affineValue n i).app U s)=z
    rw [hs,ha]
end ActualTwoDescentOriginalOverlapValueImageRebuild318
'''
S['ActualTwoDescentOriginalRationalImageBoundRebuild318']='''module
public import ActualTwoDescentOriginalOverlapValueImageRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRationalImageBoundRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalRationalAdditiveImageRebuild318
variable {K : Type*} [Field K] [CharZero K]

/-- Every actual global-section value is a regular value on the ENTIRE
intersection of the ambient open with the old common chart. -/
lemma regular_on_overlap (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    letI := ActualTwoDescentOpenRationalEvaluationRebuild318.preimage_nonempty (overlapEmbedding n) U
    ∀ z : (originalCubicScheme n).functionField,z ∈ image n i U →
      ∃ a : Γ(overlapScheme n,overlapEmbedding n ⁻¹ᵁ U),
        ActualTwoDescentOriginalOverlapValueImageRebuild318.regularValue n
          (overlapEmbedding n ⁻¹ᵁ U) a=z := by
  intro z hz
  obtain ⟨s,hs⟩ := (mem_image n i U z).mp hz
  apply (ActualTwoDescentOriginalOverlapValueImageRebuild318.full_image n i _ z).mp
  refine ⟨ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.restrictSection n i U s,?_⟩
  rw [←ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.value_square]
  exact hs

/-- The remaining global injectivity obligation is exposed exactly,
not filled by an abstract isomorphism or new hypothesis in the main theorem. -/
lemma injective_iff_restriction (n : K) (i : Fin 3) (U : (originalCubicScheme n).Opens)
    [Nonempty U] :
    Function.Injective (ActualTwoDescentOriginalGlobalRationalValueRebuild318.value n i U) ↔
      Function.Injective (ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.restrictSection n i U) := by
  constructor
  · intro h s t hst
    exact h ((ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.eq_iff_section n i U s t).mpr hst)
  · intro h s t hst
    exact h ((ActualTwoDescentOriginalRationalRestrictionSquareRebuild318.eq_iff_section n i U s t).mp hst)
end ActualTwoDescentOriginalRationalImageBoundRebuild318
'''
for n,s in S.items():(p/(n+'.lean')).write_text(s)
print('wrote',len(S),'new files; repaired source module Hom.app_smul')
