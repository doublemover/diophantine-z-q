module
public import VaryingWordGlobalAmbient318
public section
noncomputable section
namespace VaryingWordGlobalClosedQuotient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "X" => VaryingWordGlobalAmbient318.ambient R A ι
local notation "u" => VaryingWordChartGluing318.into R A ι
local notation "p" => VaryingWordGlobalAmbient318.projection R A ι
local notation "a" => VaryingWordGlobalAmbient318.chartInto R A ι
local notation "j" => VaryingWordGlobalAmbient318.into R A ι

/-- Actual ambient tensor-source charts cover the global source product. -/
@[expose] def cover : X.OpenCover where
  I₀ := ι → List A
  X := VaryingWordGlobalAmbient318.chart R A ι
  f := a
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun w => inferInstance⟩
    intro x
    obtain ⟨w,y,hy⟩ := ((VaryingWordChartGluing318.cover R A ι).pullback₁ p).exists_eq x
    let h := VaryingWordGlobalAmbient318.chart_cartesian R A ι w
    refine ⟨w,h.isoPullback.inv y,?_⟩
    have he := congrArg (fun k : pullback p (u w) ⟶ X => k y) h.isoPullback_inv_fst
    exact he.trans hy

/-- The global family is a closed subscheme of the ORIGINAL source product,
not merely an abstract finite-flat scheme with the same ranks. -/
instance closed : IsClosedImmersion j := by
  apply IsZariskiLocalAtTarget.of_openCover (cover R A ι)
  intro w
  have h := VaryingWordGlobalAmbient318.quotient_cartesian R A ι w
  have hc : IsClosedImmersion (h.isoPullback.inv ≫
      VaryingNormalizedUniversalFamily318.intoSource R A ι w) := inferInstance
  simpa only [h.isoPullback_inv_snd] using hc

/-- The full scheme-theoretic original-source ideal, without radicalizing. -/
@[expose] def idealSheaf : X.IdealSheafData := j.ker
@[expose] def subschemeIso : VaryingWordFamilyGluing318.scheme R A ι ≅
    (idealSheaf R A ι).subscheme := asIso j.toImage
@[reassoc] lemma subschemeIso_into : (subschemeIso R A ι).hom ≫
    (idealSheaf R A ι).subschemeι=j := j.toImage_imageι
end VaryingWordGlobalClosedQuotient318
