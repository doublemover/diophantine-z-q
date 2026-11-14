module
public import LegendreCompletedPointIdentification318
public import NormalizedLegendreWholeProjection318
public section
noncomputable section
namespace LegendreLiteralCompletedAtlas318
open LegendreCompletedPointIdentification318 LegendrePlaneOverlap318
open LegendreFiniteComplexAtlas318 NormalizedLegendreProjectiveModel318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- Literal original (t,y) coordinates, not the shifted native x silently
renamed t. This identifies the independently topologized finite chart. -/
@[expose] def literalFiniteEquiv : Plane l ≃ NormalizedLegendreFieldPoints318.FinitePoints l :=
  (finiteSolutions l).trans (NormalizedLegendreFieldPoints318.translated l).symm
lemma literalFinite_value (p : Plane l) :
    (literalFiniteEquiv l p).val=(p.val.1+shift l,p.val.2) := rfl
lemma literalFinite_inverse (p : NormalizedLegendreFieldPoints318.FinitePoints l) :
    ((literalFiniteEquiv l).symm p).val=(p.val.1-shift l,p.val.2) := rfl

@[expose] def literalFiniteHomeomorph : Plane l ≃ₜ NormalizedLegendreFieldPoints318.FinitePoints l where
  toEquiv := literalFiniteEquiv l
  continuous_toFun := by
    exact ((continuous_subtype_val.fst.add continuous_const).prodMk
      continuous_subtype_val.snd).subtype_mk (fun p=>(literalFiniteEquiv l p).property)
  continuous_invFun := by
    exact ((continuous_subtype_val.fst.sub continuous_const).prodMk
      continuous_subtype_val.snd).subtype_mk (fun p=>((literalFiniteEquiv l).symm p).property)

/-- ALL complex points, retaining the actual original infinity. -/
@[expose] def literalCompletedEquiv : CompletedPlane l ≃
    Option (NormalizedLegendreFieldPoints318.FinitePoints l) :=
  (optionEquivalence l).trans (Equiv.optionCongr (literalFiniteEquiv l))
lemma literal_finite (p : Plane l) :
    literalCompletedEquiv l (finiteChart l p)=some (literalFiniteEquiv l p) := by
  change (Equiv.optionCongr (literalFiniteEquiv l))
    (optionEquivalence l (finiteChart l p))=_
  rw [option_finite]
  rfl
lemma literal_origin : literalCompletedEquiv l (infinityChart l (origin l))=none := by
  change (Equiv.optionCongr (literalFiniteEquiv l))
    (optionEquivalence l (infinityChart l (origin l)))=_
  rw [option_origin]
  rfl

lemma finite_scheme (p : Plane l) : schemeEquivalence l (finiteChart l p)=
    NormalizedLegendreFieldPoints318.schemeEquiv l (some (literalFiniteEquiv l p)) := by
  rw [scheme_finite,NormalizedLegendreFieldPoints318.scheme_some]
  change CompletedFieldPoints318.finiteInclusion (A l) (B l)
    ((AffineSchemeSolutions318.schemeSolutionEquiv (A l) (B l)).symm (finiteSolutions l p))=
    CompletedFieldPoints318.finiteInclusion (A l) (B l)
      ((AffineSchemeSolutions318.schemeSolutionEquiv (A l) (B l)).symm
        (NormalizedLegendreFieldPoints318.translated l
          ((NormalizedLegendreFieldPoints318.translated l).symm (finiteSolutions l p))))
  rw [Equiv.apply_symm_apply]

/-- Same actual scheme-valued points as the previously constructed full
Legendre projection, not an independent abstract cubic with the same j. -/
theorem actual_scheme (p : CompletedPlane l) :
    schemeEquivalence l p=NormalizedLegendreFieldPoints318.schemeEquiv l
      (literalCompletedEquiv l p) := by
  rcases chart_cover l p with ⟨q,rfl⟩|⟨q,rfl⟩
  · rw [literal_finite]
    exact finite_scheme l q
  · by_cases hv:q.val.2=0
    · rw [infinity_zero l q hv,literal_origin,scheme_origin]
      rfl
    · rw [←(chart_identification l (toFinite l q) q).mpr
        ⟨toFinite_nonzero l q hv,right_inverse l q hv⟩,literal_finite]
      exact finite_scheme l (toFinite l q)
end LegendreLiteralCompletedAtlas318
