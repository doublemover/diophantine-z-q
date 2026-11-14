module
public import LegendreActualPeriodScaling318
public import LegendreNativeGermHolomorphy318
public section
noncomputable section
namespace LegendrePeriodScalingPoints318
open ComplexAffineFreeTranslation318
open scoped Topology
variable (L:AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
variable (l:ℂ) [Fact (l≠0 ∧ l≠1)] (u:ℂˣ)
variable (hA:NormalizedLegendreProjectiveModel318.A l=(u:ℂ)^4*OriginalPeriodProjectiveModel318.A L)
variable (hB:NormalizedLegendreProjectiveModel318.B l=(u:ℂ)^6*OriginalPeriodProjectiveModel318.B L)

lemma finite_equation (x y:ℂ) :
    LegendreIndependentGraphs318.finiteEquation l ((u:ℂ)^2*x,(u:ℂ)^3*y)=
      (u:ℂ)^6*OriginalPeriodIndependentGraphs318.finiteEquation L (x,y) := by
  dsimp [LegendreIndependentGraphs318.finiteEquation,OriginalPeriodIndependentGraphs318.finiteEquation]
  rw [hA,hB]
  ring
lemma infinity_equation (U V:ℂ) :
    LegendreIndependentGraphs318.infinityEquation l (U/(u:ℂ),V/(u:ℂ)^3)=
      OriginalPeriodIndependentGraphs318.infinityEquation L (U,V)/(u:ℂ)^3 := by
  dsimp [LegendreIndependentGraphs318.infinityEquation,OriginalPeriodIndependentGraphs318.infinityEquation]
  rw [hA,hB]
  field_simp [Units.ne_zero u]
  <;> ring

/-- Actual short-model coordinate scaling; all finite points, including
branch points, are retained. -/
@[expose] def finite (p:OriginalPeriodFiniteComplexAtlas318.Plane L) :
    LegendreFiniteComplexAtlas318.Plane l :=
  ⟨((u:ℂ)^2*p.val.1,(u:ℂ)^3*p.val.2),by rw [finite_equation L l u hA hB,p.property,mul_zero]⟩
@[expose] def finiteInverse (p:LegendreFiniteComplexAtlas318.Plane l) :
    OriginalPeriodFiniteComplexAtlas318.Plane L := by
  refine ⟨(p.val.1/(u:ℂ)^2,p.val.2/(u:ℂ)^3),?_⟩
  have h:=finite_equation L l u hA hB (p.val.1/(u:ℂ)^2) (p.val.2/(u:ℂ)^3)
  have hh:LegendreIndependentGraphs318.finiteEquation l
      ((u:ℂ)^2*(p.val.1/(u:ℂ)^2),(u:ℂ)^3*(p.val.2/(u:ℂ)^3))=0:=by
    have hc:((u:ℂ)^2*(p.val.1/(u:ℂ)^2),(u:ℂ)^3*(p.val.2/(u:ℂ)^3))=p.val:=by
      apply Prod.ext <;> field_simp [Units.ne_zero u]
    rw [hc]
    exact p.property
  rw [h] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (Units.ne_zero u))
@[expose] def finiteEquiv : OriginalPeriodFiniteComplexAtlas318.Plane L≃
    LegendreFiniteComplexAtlas318.Plane l where
  toFun:=finite L l u hA hB
  invFun:=finiteInverse L l u hA hB
  left_inv p:=by
    apply Subtype.ext
    apply Prod.ext <;> dsimp [finite,finiteInverse] <;> field_simp [Units.ne_zero u]
  right_inv p:=by
    apply Subtype.ext
    apply Prod.ext <;> dsimp [finite,finiteInverse] <;> field_simp [Units.ne_zero u]

/-- Scaling of the actual infinity chart is U↦U/u,V↦V/u³, not the
finite coordinate powers. Its origin is preserved explicitly. -/
@[expose] def infinity (p:OriginalPeriodPlaneOverlap318.InfinityPlane L) :
    LegendrePlaneOverlap318.InfinityPlane l :=
  ⟨(p.val.1/(u:ℂ),p.val.2/(u:ℂ)^3),by rw [infinity_equation L l u hA hB,p.property,zero_div]⟩
lemma infinity_origin : infinity L l u hA hB (OriginalPeriodPlaneOverlap318.origin L)=
    LegendrePlaneOverlap318.origin l := by
  apply Subtype.ext
  simp [infinity,OriginalPeriodPlaneOverlap318.origin,LegendrePlaneOverlap318.origin]

/-- Full completed point equivalence on the actual two independently
glued models, with the unique infinity point retained. -/
@[expose] def equivalence : OriginalPeriodPlaneOverlap318.CompletedPlane L≃
    LegendrePlaneOverlap318.CompletedPlane l :=
  (OriginalPeriodCompletedPointIdentification318.optionEquivalence L).trans
    ((Equiv.optionCongr (finiteEquiv L l u hA hB)).trans
      (LegendreCompletedPointIdentification318.optionEquivalence l).symm)
lemma finite_value (p:OriginalPeriodFiniteComplexAtlas318.Plane L) :
    equivalence L l u hA hB (OriginalPeriodPlaneOverlap318.finiteChart L p)=
      LegendrePlaneOverlap318.finiteChart l (finite L l u hA hB p) := by
  apply (LegendreCompletedPointIdentification318.optionEquivalence l).injective
  change LegendreCompletedPointIdentification318.optionEquivalence l
    ((LegendreCompletedPointIdentification318.optionEquivalence l).symm
      ((Equiv.optionCongr (finiteEquiv L l u hA hB))
        (OriginalPeriodCompletedPointIdentification318.optionEquivalence L
          (OriginalPeriodPlaneOverlap318.finiteChart L p))))=_
  rw [Equiv.apply_symm_apply,OriginalPeriodCompletedPointIdentification318.option_finite,
    LegendreCompletedPointIdentification318.option_finite]
  rfl
lemma origin_value :
    equivalence L l u hA hB (OriginalPeriodPlaneOverlap318.infinityChart L
      (OriginalPeriodPlaneOverlap318.origin L))=
      LegendrePlaneOverlap318.infinityChart l (LegendrePlaneOverlap318.origin l) := by
  apply (LegendreCompletedPointIdentification318.optionEquivalence l).injective
  change LegendreCompletedPointIdentification318.optionEquivalence l
    ((LegendreCompletedPointIdentification318.optionEquivalence l).symm
      ((Equiv.optionCongr (finiteEquiv L l u hA hB))
        (OriginalPeriodCompletedPointIdentification318.optionEquivalence L
          (OriginalPeriodPlaneOverlap318.infinityChart L (OriginalPeriodPlaneOverlap318.origin L)))))=_
  rw [Equiv.apply_symm_apply,OriginalPeriodCompletedPointIdentification318.option_origin,
    LegendreCompletedPointIdentification318.option_origin]
  rfl

/-- Actual finite/infinity coordinate scaling agrees on the genuine
localization overlap. This is the gluing check, not equality of j alone. -/
lemma infinity_value (q:OriginalPeriodPlaneOverlap318.InfinityPlane L) :
    equivalence L l u hA hB (OriginalPeriodPlaneOverlap318.infinityChart L q)=
      LegendrePlaneOverlap318.infinityChart l (infinity L l u hA hB q) := by
  by_cases hv:q.val.2=0
  · rw [OriginalPeriodCompletedPointIdentification318.infinity_zero L q hv,infinity_origin,
      origin_value]
  · rw [←(OriginalPeriodPlaneOverlap318.chart_identification L
        (OriginalPeriodPlaneOverlap318.toFinite L q) q).mpr
      ⟨OriginalPeriodPlaneOverlap318.toFinite_nonzero L q hv,
        OriginalPeriodPlaneOverlap318.right_inverse L q hv⟩,finite_value]
    apply (LegendrePlaneOverlap318.chart_identification l _ _).mpr
    have hy:(finite L l u hA hB (OriginalPeriodPlaneOverlap318.toFinite L q)).val.2≠0:=by
      change (u:ℂ)^3*(OriginalPeriodPlaneOverlap318.toFinite L q).val.2≠0
      exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero u))
        (OriginalPeriodPlaneOverlap318.toFinite_nonzero L q hv)
    refine ⟨hy,?_⟩
    apply Subtype.ext
    rw [LegendrePlaneOverlap318.toInfinity_value l _ hy]
    change (((u:ℂ)^2*(OriginalPeriodPlaneOverlap318.toFinite L q).val.1)/
      ((u:ℂ)^3*(OriginalPeriodPlaneOverlap318.toFinite L q).val.2),
      1/((u:ℂ)^3*(OriginalPeriodPlaneOverlap318.toFinite L q).val.2))=_
    rw [OriginalPeriodPlaneOverlap318.toFinite_value L q hv]
    apply Prod.ext <;> dsimp [infinity] <;> field_simp [hv,Units.ne_zero u] <;> ring
end LegendrePeriodScalingPoints318
