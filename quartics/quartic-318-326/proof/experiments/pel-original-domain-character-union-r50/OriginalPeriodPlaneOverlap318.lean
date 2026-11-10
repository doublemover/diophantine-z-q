module
public import OriginalPeriodFiniteComplexAtlas318
public import LocalHolomorphicSquareRoot318
public import TwoChartGluing318
public section
noncomputable section
namespace OriginalPeriodPlaneOverlap318
open OriginalPeriodIndependentGraphs318 OriginalPeriodProjectiveModel318
open OriginalPeriodFiniteComplexAtlas318 AnalyticZeroLocusChart318
open ComplexAffineFreeTranslation318 Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Actual infinity affine plane, in its independent induced topology. -/
abbrev InfinityPlane := ZeroLocus (infinityEquation L)
@[expose] def origin : InfinityPlane L := ⟨(0,0),by simp [infinityEquation]⟩
/-- Only a total-function fallback outside the finite chart overlap.
Its value has no role in either overlap, chart, or gluing relation. -/
@[expose] def fallback : Plane L := ⟨(0,Complex.sqrt (B L)),by
  simp only [finiteEquation,zero_pow (by decide : 3≠0),mul_zero,sub_zero]
  rw [LocalHolomorphicSquareRoot318.sqrt_square,sub_self]⟩

lemma into_infinity_equation (p : Plane L) (hy : p.val.2≠0) :
    infinityEquation L (p.val.1/p.val.2,1/p.val.2)=0 := by
  have h := p.property
  dsimp [infinityEquation,finiteEquation] at *
  field_simp [hy]
  linear_combination h
lemma into_finite_equation (p : InfinityPlane L) (hv : p.val.2≠0) :
    finiteEquation L (p.val.1/p.val.2,1/p.val.2)=0 := by
  have h := p.property
  dsimp [infinityEquation,finiteEquation] at *
  field_simp [hv]
  linear_combination h

@[expose] def toInfinity (p : Plane L) : InfinityPlane L :=
  if hy:p.val.2≠0 then ⟨(p.val.1/p.val.2,1/p.val.2),into_infinity_equation L p hy⟩ else origin L
@[expose] def toFinite (p : InfinityPlane L) : Plane L :=
  if hv:p.val.2≠0 then ⟨(p.val.1/p.val.2,1/p.val.2),into_finite_equation L p hv⟩ else fallback L
lemma toInfinity_value (p : Plane L) (hy : p.val.2≠0) :
    (toInfinity L p).val=(p.val.1/p.val.2,1/p.val.2) := by
  dsimp [toInfinity];rw [dif_pos hy]
lemma toFinite_value (p : InfinityPlane L) (hv : p.val.2≠0) :
    (toFinite L p).val=(p.val.1/p.val.2,1/p.val.2) := by
  dsimp [toFinite];rw [dif_pos hv]
lemma toInfinity_nonzero (p : Plane L) (hy : p.val.2≠0) : (toInfinity L p).val.2≠0 := by
  rw [toInfinity_value L p hy]
  exact div_ne_zero one_ne_zero hy
lemma toFinite_nonzero (p : InfinityPlane L) (hv : p.val.2≠0) : (toFinite L p).val.2≠0 := by
  rw [toFinite_value L p hv]
  exact div_ne_zero one_ne_zero hv
lemma left_inverse (p : Plane L) (hy : p.val.2≠0) : toFinite L (toInfinity L p)=p := by
  apply Subtype.ext
  rw [toFinite_value L _ (toInfinity_nonzero L p hy),toInfinity_value L p hy]
  apply Prod.ext <;> dsimp <;> field_simp [hy]
lemma right_inverse (p : InfinityPlane L) (hv : p.val.2≠0) : toInfinity L (toFinite L p)=p := by
  apply Subtype.ext
  rw [toInfinity_value L _ (toFinite_nonzero L p hv),toFinite_value L p hv]
  apply Prod.ext <;> dsimp <;> field_simp [hv]

lemma toInfinity_continuous : ContinuousOn (toInfinity L) {p | p.val.2≠0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h1 : Continuous (fun p : {p : Plane L // p.val.2≠0} => p.val.val.1) := by fun_prop
  have h2 : Continuous (fun p : {p : Plane L // p.val.2≠0} => p.val.val.2) := by fun_prop
  have hc := ((h1.div h2 (fun p=>p.property)).prodMk
    (continuous_const.div h2 (fun p=>p.property))).subtype_mk
      (fun p : {p : Plane L // p.val.2≠0} => into_infinity_equation L p.val p.property)
  convert hc using 1
  funext p
  apply Subtype.ext
  exact toInfinity_value L p.val p.property
lemma toFinite_continuous : ContinuousOn (toFinite L) {p | p.val.2≠0} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h1 : Continuous (fun p : {p : InfinityPlane L // p.val.2≠0} => p.val.val.1) := by fun_prop
  have h2 : Continuous (fun p : {p : InfinityPlane L // p.val.2≠0} => p.val.val.2) := by fun_prop
  have hc := ((h1.div h2 (fun p=>p.property)).prodMk
    (continuous_const.div h2 (fun p=>p.property))).subtype_mk
      (fun p : {p : InfinityPlane L // p.val.2≠0} => into_finite_equation L p.val p.property)
  convert hc using 1
  funext p
  apply Subtype.ext
  exact toFinite_value L p.val p.property

/-- Actual algebraic coordinate transition, as an independent topological
open overlap. It glues only the original D(y) and D(v), not arbitrary copies. -/
@[expose] def overlap : OpenPartialHomeomorph (Plane L) (InfinityPlane L) where
  toFun := toInfinity L
  invFun := toFinite L
  source := {p | p.val.2≠0}
  target := {p | p.val.2≠0}
  map_source' := toInfinity_nonzero L
  map_target' := toFinite_nonzero L
  left_inv' := left_inverse L
  right_inv' := right_inverse L
  open_source := isOpen_ne (by fun_prop) continuous_const
  open_target := isOpen_ne (by fun_prop) continuous_const
  continuousOn_toFun := toInfinity_continuous L
  continuousOn_invFun := toFinite_continuous L

/-- Independent complex-point topology glued from the TWO ACTUAL
polynomial charts and original algebraic coordinate transition. -/
abbrev CompletedPlane := TwoChartGluing318.Space (overlap L)
@[expose] def finiteChart : Plane L → CompletedPlane L := TwoChartGluing318.left (overlap L)
@[expose] def infinityChart : InfinityPlane L → CompletedPlane L := TwoChartGluing318.right (overlap L)
theorem finite_open : IsOpenEmbedding (finiteChart L) := TwoChartGluing318.left_isOpenEmbedding _
theorem infinity_open : IsOpenEmbedding (infinityChart L) := TwoChartGluing318.right_isOpenEmbedding _
theorem chart_cover (p : CompletedPlane L) :
    (∃q,finiteChart L q=p) ∨ (∃q,infinityChart L q=p) := TwoChartGluing318.jointly_surjective _ p
theorem chart_identification (p : Plane L) (q : InfinityPlane L) :
    finiteChart L p=infinityChart L q ↔ p.val.2≠0 ∧ toInfinity L p=q :=
  TwoChartGluing318.left_eq_right_iff _ p q
end OriginalPeriodPlaneOverlap318
