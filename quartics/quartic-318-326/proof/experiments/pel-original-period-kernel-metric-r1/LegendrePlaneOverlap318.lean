module
public import LegendreFiniteComplexAtlas318
public import LocalHolomorphicSquareRoot318
public import TwoChartGluing318
public section
noncomputable section
namespace LegendrePlaneOverlap318
open LegendreIndependentGraphs318 NormalizedLegendreProjectiveModel318
open LegendreFiniteComplexAtlas318 AnalyticZeroLocusChart318
open Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- Actual infinity affine plane, in its independent induced topology. -/
abbrev InfinityPlane := ZeroLocus (infinityEquation l)
@[expose] def origin : InfinityPlane l := ⟨(0,0),by simp [infinityEquation]⟩
/-- Only a total-function fallback outside the finite chart overlap.
Its value has no role in either overlap, chart, or gluing relation. -/
@[expose] def fallback : Plane l := ⟨(0,Complex.sqrt (B l)),by
  simp only [finiteEquation,zero_pow (by decide : 3≠0),mul_zero,sub_zero]
  rw [LocalHolomorphicSquareRoot318.sqrt_square,sub_self]⟩

lemma into_infinity_equation (p : Plane l) (hy : p.val.2≠0) :
    infinityEquation l (p.val.1/p.val.2,1/p.val.2)=0 := by
  have h := p.property
  dsimp [infinityEquation,finiteEquation] at *
  field_simp [hy]
  linear_combination h
lemma into_finite_equation (p : InfinityPlane l) (hv : p.val.2≠0) :
    finiteEquation l (p.val.1/p.val.2,1/p.val.2)=0 := by
  have h := p.property
  dsimp [infinityEquation,finiteEquation] at *
  field_simp [hv]
  linear_combination h

@[expose] def toInfinity (p : Plane l) : InfinityPlane l :=
  if hy:p.val.2≠0 then ⟨(p.val.1/p.val.2,1/p.val.2),into_infinity_equation l p hy⟩ else origin l
@[expose] def toFinite (p : InfinityPlane l) : Plane l :=
  if hv:p.val.2≠0 then ⟨(p.val.1/p.val.2,1/p.val.2),into_finite_equation l p hv⟩ else fallback l
lemma toInfinity_value (p : Plane l) (hy : p.val.2≠0) :
    (toInfinity l p).val=(p.val.1/p.val.2,1/p.val.2) := by
  dsimp [toInfinity];rw [dif_pos hy]
lemma toFinite_value (p : InfinityPlane l) (hv : p.val.2≠0) :
    (toFinite l p).val=(p.val.1/p.val.2,1/p.val.2) := by
  dsimp [toFinite];rw [dif_pos hv]
lemma toInfinity_nonzero (p : Plane l) (hy : p.val.2≠0) : (toInfinity l p).val.2≠0 := by
  rw [toInfinity_value l p hy]
  exact div_ne_zero one_ne_zero hy
lemma toFinite_nonzero (p : InfinityPlane l) (hv : p.val.2≠0) : (toFinite l p).val.2≠0 := by
  rw [toFinite_value l p hv]
  exact div_ne_zero one_ne_zero hv
lemma left_inverse (p : Plane l) (hy : p.val.2≠0) : toFinite l (toInfinity l p)=p := by
  apply Subtype.ext
  rw [toFinite_value l _ (toInfinity_nonzero l p hy),toInfinity_value l p hy]
  apply Prod.ext <;> dsimp <;> field_simp [hy]
lemma right_inverse (p : InfinityPlane l) (hv : p.val.2≠0) : toInfinity l (toFinite l p)=p := by
  apply Subtype.ext
  rw [toInfinity_value l _ (toFinite_nonzero l p hv),toFinite_value l p hv]
  apply Prod.ext <;> dsimp <;> field_simp [hv]

lemma toInfinity_continuous : ContinuousOn (toInfinity l) {p | p.val.2≠0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h1 : Continuous (fun p : {p : Plane l // p.val.2≠0} => p.val.val.1) := by fun_prop
  have h2 : Continuous (fun p : {p : Plane l // p.val.2≠0} => p.val.val.2) := by fun_prop
  have hc := ((h1.div h2 (fun p=>p.property)).prodMk
    (continuous_const.div h2 (fun p=>p.property))).subtype_mk
      (fun p : {p : Plane l // p.val.2≠0} => into_infinity_equation l p.val p.property)
  convert hc using 1
  funext p
  apply Subtype.ext
  exact toInfinity_value l p.val p.property
lemma toFinite_continuous : ContinuousOn (toFinite l) {p | p.val.2≠0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h1 : Continuous (fun p : {p : InfinityPlane l // p.val.2≠0} => p.val.val.1) := by fun_prop
  have h2 : Continuous (fun p : {p : InfinityPlane l // p.val.2≠0} => p.val.val.2) := by fun_prop
  have hc := ((h1.div h2 (fun p=>p.property)).prodMk
    (continuous_const.div h2 (fun p=>p.property))).subtype_mk
      (fun p : {p : InfinityPlane l // p.val.2≠0} => into_finite_equation l p.val p.property)
  convert hc using 1
  funext p
  apply Subtype.ext
  exact toFinite_value l p.val p.property

/-- Actual algebraic coordinate transition, as an independent topological
open overlap. It glues only the original D(y) and D(v), not arbitrary copies. -/
@[expose] def overlap : OpenPartialHomeomorph (Plane l) (InfinityPlane l) where
  toFun := toInfinity l
  invFun := toFinite l
  source := {p | p.val.2≠0}
  target := {p | p.val.2≠0}
  map_source' := toInfinity_nonzero l
  map_target' := toFinite_nonzero l
  left_inv' := left_inverse l
  right_inv' := right_inverse l
  open_source := isOpen_ne (by fun_prop) continuous_const
  open_target := isOpen_ne (by fun_prop) continuous_const
  continuousOn_toFun := toInfinity_continuous l
  continuousOn_invFun := toFinite_continuous l

/-- Independent complex-point topology glued from the TWO ACTUAL
polynomial charts and original algebraic coordinate transition. -/
abbrev CompletedPlane := TwoChartGluing318.Space (overlap l)
@[expose] def finiteChart : Plane l → CompletedPlane l := TwoChartGluing318.left (overlap l)
@[expose] def infinityChart : InfinityPlane l → CompletedPlane l := TwoChartGluing318.right (overlap l)
theorem finite_open : IsOpenEmbedding (finiteChart l) := TwoChartGluing318.left_isOpenEmbedding _
theorem infinity_open : IsOpenEmbedding (infinityChart l) := TwoChartGluing318.right_isOpenEmbedding _
theorem chart_cover (p : CompletedPlane l) :
    (∃q,finiteChart l q=p) ∨ (∃q,infinityChart l q=p) := TwoChartGluing318.jointly_surjective _ p
theorem chart_identification (p : Plane l) (q : InfinityPlane l) :
    finiteChart l p=infinityChart l q ↔ p.val.2≠0 ∧ toInfinity l p=q :=
  TwoChartGluing318.left_eq_right_iff _ p q
end LegendrePlaneOverlap318
