module
public import VaryingWordFamilyGluing318
public section
noncomputable section
namespace VaryingWordGlobalFamilyProjection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "p" => VaryingNormalizedUniversalFamily318.projection R A ι
local notation "inc" => VaryingWordOverlapFamily318.into R A ι
local notation "proj" => VaryingWordOverlapFamily318.projection R A ι
local notation "baseinc" => VaryingNormalizedOverlapScheme318.into R A ι
local notation "baset" => VaryingNormalizedOverlapScheme318.transition R A ι
local notation "basechart" => VaryingWordChartGluing318.into R A ι

/-- The actual global quotient-family scheme maps to the actual glued
word-chart parameter. Both local projection equations are retained. -/
@[expose] def projection : VaryingWordFamilyGluing318.scheme R A ι ⟶ VaryingWordChartGluing318.scheme R A ι := by
  fapply Multicoequalizer.desc
  · exact fun w => p w ≫ basechart w
  rintro ⟨w,v⟩
  change inc w v ≫ (p w ≫ basechart w)=
    ((VaryingWordFamilyTransition318.transition R A ι w v).hom ≫ inc v w) ≫ (p v ≫ basechart v)
  calc
    _=(proj w v ≫ baseinc w v) ≫ basechart w := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ basechart w)
        (VaryingWordOverlapFamily318.cartesian R A ι w v).w
    _=proj w v ≫ (baset w v ≫ baseinc v w ≫ basechart v) := by
      simpa only [Category.assoc] using congrArg (fun k => proj w v ≫ k)
        (VaryingWordChartGluing318.glue_condition R A ι w v).symm
    _=((VaryingWordFamilyTransition318.transition R A ι w v).hom ≫ proj v w) ≫
        (baseinc v w ≫ basechart v) := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ (baseinc v w ≫ basechart v))
        (VaryingWordFamilyTransition318.transition_projection R A ι w v).symm
    _=((VaryingWordFamilyTransition318.transition R A ι w v).hom ≫ inc v w) ≫ (p v ≫ basechart v) := by
      simpa only [Category.assoc] using congrArg
        (fun k => (VaryingWordFamilyTransition318.transition R A ι w v).hom ≫ k ≫ basechart v)
        (VaryingWordOverlapFamily318.cartesian R A ι v w).w.symm
@[reassoc] lemma into_projection (w : ι → List A) :
    VaryingWordFamilyGluing318.into R A ι w ≫ projection R A ι=p w ≫ basechart w :=
  Multicoequalizer.π_desc _ _ _ _ _
end VaryingWordGlobalFamilyProjection318
