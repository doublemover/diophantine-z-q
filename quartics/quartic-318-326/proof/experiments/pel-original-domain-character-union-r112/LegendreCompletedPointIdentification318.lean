module
public import LegendreCompletedComplexAtlas318
public section
noncomputable section
namespace LegendreCompletedPointIdentification318
open LegendrePlaneOverlap318 LegendreIndependentGraphs318
open NormalizedLegendreProjectiveModel318
open LegendreFiniteComplexAtlas318
set_option maxHeartbeats 2400000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- The ORIGINAL infinity equation has exactly one point off D(v). -/
lemma infinity_zero (q : InfinityPlane l) (hv : q.val.2=0) : q=origin l := by
  have h := q.property
  dsimp [infinityEquation] at h
  rw [hv] at h
  have hu : q.val.1=0 := by
    have hp : q.val.1^3=0 := by simpa using h.symm
    exact pow_eq_zero hp
  apply Subtype.ext
  exact Prod.ext hu hv

lemma finite_ne_origin (p : Plane l) : finiteChart l p≠infinityChart l (origin l) := by
  intro he
  obtain ⟨hy,hq⟩ := (chart_identification l p (origin l)).mp he
  have hn := toInfinity_nonzero l p hy
  rw [hq] at hn
  exact hn rfl

/-- Classify the independently glued target by its actual finite chart
and the unique actual infinity point, not by transporting a torus topology. -/
@[expose] def fromOption : Option (Plane l) → CompletedPlane l
  | none => infinityChart l (origin l)
  | some p => finiteChart l p

lemma fromOption_bijective : Function.Bijective (fromOption l) := by
  constructor
  · intro p q he
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q => exact (finite_ne_origin l q he.symm).elim
    | some p =>
      cases q with
      | none => exact (finite_ne_origin l p he).elim
      | some q => exact congrArg some ((finite_open l).injective he)
  · intro z
    rcases chart_cover l z with ⟨p,rfl⟩ | ⟨q,rfl⟩
    · exact ⟨some p,rfl⟩
    · by_cases hv : q.val.2=0
      · exact ⟨none,congrArg (infinityChart l) (infinity_zero l q hv).symm⟩
      · exact ⟨some (toFinite l q),(chart_identification l _ q).mpr
          ⟨toFinite_nonzero l q hv,right_inverse l q hv⟩⟩

@[expose] def optionEquivalence : CompletedPlane l ≃ Option (Plane l) :=
  (Equiv.ofBijective (fromOption l) (fromOption_bijective l)).symm
lemma option_finite (p : Plane l) : optionEquivalence l (finiteChart l p)=some p :=
  (optionEquivalence l).apply_symm_apply (some p)
lemma option_origin : optionEquivalence l (infinityChart l (origin l))=none :=
  (optionEquivalence l).apply_symm_apply none
lemma option_infinity (q : InfinityPlane l) (hv : q.val.2≠0) :
    optionEquivalence l (infinityChart l q)=some (toFinite l q) := by
  rw [← (chart_identification l (toFinite l q) q).mpr
    ⟨toFinite_nonzero l q hv,right_inverse l q hv⟩]
  exact option_finite l _

/-- Identity on actual x,y coordinates between the independent plane
and the independent scheme's literal affine equation functor. -/
@[expose] def finiteSolutions : Plane l ≃ AffineEquationFunctor318.Solutions (S:=ℂ) (A l) (B l) where
  toFun p := ⟨p.val,by simpa only [Algebra.algebraMap_self,RingHom.id_apply] using p.property⟩
  invFun p := ⟨p.val,by simpa only [Algebra.algebraMap_self,RingHom.id_apply] using p.property⟩
  left_inv p := rfl
  right_inv p := rfl

@[expose] def finiteScheme : Plane l ≃ AffineSchemeSolutions318.SchemePoints (K:=ℂ) (A l) (B l) :=
  (finiteSolutions l).trans (AffineSchemeSolutions318.schemeSolutionEquiv (A l) (B l)).symm

/-- The independent completed target is identified with ALL actual
complex points of the original smooth proper scheme, by genuine coordinate
functors and the actual scheme-chart coverage theorem. -/
@[expose] def schemeEquivalence : CompletedPlane l ≃
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A l) (B l) :=
  (optionEquivalence l).trans ((Equiv.optionCongr (finiteScheme l)).trans
    (CompletedFieldPoints318.completedEquiv (K:=ℂ) (A l) (B l)).symm)

lemma scheme_finite (p : Plane l) : schemeEquivalence l (finiteChart l p)=
    CompletedFieldPoints318.finiteInclusion (A l) (B l) (finiteScheme l p) := by
  change (CompletedFieldPoints318.completedEquiv (A l) (B l)).symm
    ((Equiv.optionCongr (finiteScheme l)) (optionEquivalence l (finiteChart l p)))=_
  rw [option_finite]
  rfl
lemma scheme_origin : schemeEquivalence l (infinityChart l (origin l))=
    CompletedFieldPoints318.infinityPoint (A l) (B l) := by
  change (CompletedFieldPoints318.completedEquiv (A l) (B l)).symm
    ((Equiv.optionCongr (finiteScheme l)) (optionEquivalence l (infinityChart l (origin l))))=_
  rw [option_origin]
  rfl
lemma scheme_infinity (q : InfinityPlane l) (hv : q.val.2≠0) :
    schemeEquivalence l (infinityChart l q)=
      CompletedFieldPoints318.finiteInclusion (A l) (B l) (finiteScheme l (toFinite l q)) := by
  rw [← (chart_identification l (toFinite l q) q).mpr
    ⟨toFinite_nonzero l q hv,right_inverse l q hv⟩,scheme_finite]

end LegendreCompletedPointIdentification318
