module
public import OriginalPeriodCompletedComplexAtlas318
public section
noncomputable section
namespace OriginalPeriodCompletedPointIdentification318
open OriginalPeriodPlaneOverlap318 OriginalPeriodIndependentGraphs318
open OriginalPeriodProjectiveModel318 ComplexAffineFreeTranslation318
open OriginalPeriodFiniteComplexAtlas318
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- The ORIGINAL infinity equation has exactly one point off D(v). -/
lemma infinity_zero (q : InfinityPlane L) (hv : q.val.2=0) : q=origin L := by
  have h := q.property
  dsimp [infinityEquation] at h
  rw [hv] at h
  have hu : q.val.1=0 := by
    have hp : q.val.1^3=0 := by simpa using h.symm
    exact pow_eq_zero hp
  apply Subtype.ext
  exact Prod.ext hu hv

lemma finite_ne_origin (p : Plane L) : finiteChart L p≠infinityChart L (origin L) := by
  intro he
  obtain ⟨hy,hq⟩ := (chart_identification L p (origin L)).mp he
  have hn := toInfinity_nonzero L p hy
  rw [hq] at hn
  exact hn rfl

/-- Classify the independently glued target by its actual finite chart
and the unique actual infinity point, not by transporting a torus topology. -/
@[expose] def fromOption : Option (Plane L) → CompletedPlane L
  | none => infinityChart L (origin L)
  | some p => finiteChart L p

lemma fromOption_bijective : Function.Bijective (fromOption L) := by
  constructor
  · intro p q he
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q => exact (finite_ne_origin L q he.symm).elim
    | some p =>
      cases q with
      | none => exact (finite_ne_origin L p he).elim
      | some q => exact congrArg some ((finite_open L).injective he)
  · intro z
    rcases chart_cover L z with ⟨p,rfl⟩ | ⟨q,rfl⟩
    · exact ⟨some p,rfl⟩
    · by_cases hv : q.val.2=0
      · exact ⟨none,congrArg (infinityChart L) (infinity_zero L q hv).symm⟩
      · exact ⟨some (toFinite L q),(chart_identification L _ q).mpr
          ⟨toFinite_nonzero L q hv,right_inverse L q hv⟩⟩

@[expose] def optionEquivalence : CompletedPlane L ≃ Option (Plane L) :=
  (Equiv.ofBijective (fromOption L) (fromOption_bijective L)).symm
lemma option_finite (p : Plane L) : optionEquivalence L (finiteChart L p)=some p :=
  (optionEquivalence L).apply_symm_apply (some p)
lemma option_origin : optionEquivalence L (infinityChart L (origin L))=none :=
  (optionEquivalence L).apply_symm_apply none
lemma option_infinity (q : InfinityPlane L) (hv : q.val.2≠0) :
    optionEquivalence L (infinityChart L q)=some (toFinite L q) := by
  rw [← (chart_identification L (toFinite L q) q).mpr
    ⟨toFinite_nonzero L q hv,right_inverse L q hv⟩]
  exact option_finite L _

/-- Identity on actual x,y coordinates between the independent plane
and the independent scheme's literal affine equation functor. -/
@[expose] def finiteSolutions : Plane L ≃ AffineEquationFunctor318.Solutions (S:=ℂ) (A L) (B L) where
  toFun p := ⟨p.val,by simpa only [Algebra.algebraMap_self,RingHom.id_apply] using p.property⟩
  invFun p := ⟨p.val,by simpa only [Algebra.algebraMap_self,RingHom.id_apply] using p.property⟩
  left_inv p := rfl
  right_inv p := rfl

@[expose] def finiteScheme : Plane L ≃ AffineSchemeSolutions318.SchemePoints (K:=ℂ) (A L) (B L) :=
  (finiteSolutions L).trans (AffineSchemeSolutions318.schemeSolutionEquiv (A L) (B L)).symm

/-- The independent completed target is identified with ALL actual
complex points of the original smooth proper scheme, by genuine coordinate
functors and the actual scheme-chart coverage theorem. -/
@[expose] def schemeEquivalence : CompletedPlane L ≃
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A L) (B L) :=
  (optionEquivalence L).trans ((Equiv.optionCongr (finiteScheme L)).trans
    (CompletedFieldPoints318.completedEquiv (K:=ℂ) (A L) (B L)).symm)

lemma scheme_finite (p : Plane L) : schemeEquivalence L (finiteChart L p)=
    CompletedFieldPoints318.finiteInclusion (A L) (B L) (finiteScheme L p) := by
  change (CompletedFieldPoints318.completedEquiv (A L) (B L)).symm
    ((Equiv.optionCongr (finiteScheme L)) (optionEquivalence L (finiteChart L p)))=_
  rw [option_finite]
  rfl
lemma scheme_origin : schemeEquivalence L (infinityChart L (origin L))=
    CompletedFieldPoints318.infinityPoint (A L) (B L) := by
  change (CompletedFieldPoints318.completedEquiv (A L) (B L)).symm
    ((Equiv.optionCongr (finiteScheme L)) (optionEquivalence L (infinityChart L (origin L))))=_
  rw [option_origin]
  rfl
lemma scheme_infinity (q : InfinityPlane L) (hv : q.val.2≠0) :
    schemeEquivalence L (infinityChart L q)=
      CompletedFieldPoints318.finiteInclusion (A L) (B L) (finiteScheme L (toFinite L q)) := by
  rw [← (chart_identification L (toFinite L q) q).mpr
    ⟨toFinite_nonzero L q hv,right_inverse L q hv⟩,scheme_finite]

/-- The original torus-to-scheme point map now lands in the INDEPENDENT
completed target. Its exact original finite coordinates and pole are
proved below, rather than used to define the target topology or atlas. -/
@[expose] def originalPoint : Torus L → CompletedPlane L :=
  fun q => (schemeEquivalence L).symm (OriginalPeriodCompletedSchemeBijection318.point L q)
lemma original_scheme (q : Torus L) : schemeEquivalence L (originalPoint L q)=
    OriginalPeriodCompletedSchemeBijection318.point L q :=
  (schemeEquivalence L).apply_symm_apply _
lemma original_zero : originalPoint L 0=infinityChart L (origin L) := by
  apply (schemeEquivalence L).injective
  rw [original_scheme,OriginalPeriodCompletedSchemeBijection318.point_zero,scheme_origin]

@[expose] def originalFinite (q : {q : Torus L // q≠0}) : Plane L :=
  (finiteScheme L).symm (OriginalPeriodFiniteSchemeBijection318.finiteEquivalence L q)
lemma original_nonzero (q : Torus L) (hq : q≠0) :
    originalPoint L q=finiteChart L (originalFinite L ⟨q,hq⟩) := by
  apply (schemeEquivalence L).injective
  rw [original_scheme,OriginalPeriodCompletedSchemeBijection318.point_nonzero L q hq,scheme_finite]
  exact congrArg (CompletedFieldPoints318.finiteInclusion (A L) (B L))
    ((finiteScheme L).apply_symm_apply _).symm
lemma original_coordinates (q : {q : Torus L // q≠0}) :
    (originalFinite L q).val=(OriginalPeriodWeierstrassCoordinates318.x L q.val,
      OriginalPeriodWeierstrassCoordinates318.y L q.val/2) := by
  change ((finiteSolutions L).symm
    ((AffineSchemeSolutions318.schemeSolutionEquiv (A L) (B L))
      ((AffineSchemeSolutions318.schemeSolutionEquiv (A L) (B L)).symm
        (OriginalPeriodFiniteSchemeBijection318.nativeSolutions L
          (OriginalPeriodWeierstrassCoordinates318.affinePoint L q))))).val=_
  rw [Equiv.apply_symm_apply]
  rfl

theorem original_bijective : Function.Bijective (originalPoint L) :=
  (schemeEquivalence L).symm.bijective.comp
    ⟨OriginalPeriodCompletedSchemeBijection318.point_injective L,
      OriginalPeriodCompletedSchemeBijection318.point_surjective L⟩
end OriginalPeriodCompletedPointIdentification318
