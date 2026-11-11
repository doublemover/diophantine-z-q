module
public import PELOriginalComparisonHomeomorph318
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Topology.Homeomorph.Lemmas
public section
noncomputable section
namespace PELOriginalPolygonDisk318
open Set Filter Metric
open scoped Topology
open PELDirichletOriginalUnits318 PELOriginalDirichletPolygon318
open PELStrictPolygonExtension318 PELActualPolygonHomeomorph318
set_option maxHeartbeats 1800000
@[expose] def strictPlane : Set (ℝ × ℝ) := {P | strictInequalities P.1 P.2}

theorem strictPlane_open : IsOpen strictPlane := by
  change IsOpen {P : ℝ × ℝ | ∀ (j : Fin 8) (ε δ : Bool),
    (rowFirst j:ℝ)*((sign ε:ℝ)*P.1)+(rowSecond j:ℝ)*((sign δ:ℝ)*P.2)<(rowConstant j:ℝ)}
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite (fun j => isOpen_iInter_of_finite (fun ε =>
    isOpen_iInter_of_finite (fun δ => isOpen_lt
      ((continuous_const.mul (continuous_const.mul continuous_fst)).add
        (continuous_const.mul (continuous_const.mul continuous_snd))) continuous_const)))

theorem strictPlane_subset : strictPlane ⊆ planePolygon :=
  fun P hP => weak_of_strict P.1 P.2 hP

theorem polygon_closed : IsClosed planePolygon := by
  change IsClosed {P : ℝ × ℝ | ∀ (j : Fin 8) (ε δ : Bool),
    (rowFirst j:ℝ)*((sign ε:ℝ)*P.1)+(rowSecond j:ℝ)*((sign δ:ℝ)*P.2)≤(rowConstant j:ℝ)}
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun j => isClosed_iInter (fun ε => isClosed_iInter (fun δ =>
    isClosed_le ((continuous_const.mul (continuous_const.mul continuous_fst)).add
      (continuous_const.mul (continuous_const.mul continuous_snd))) continuous_const)))

theorem polygon_convex : Convex ℝ planePolygon := by
  intro P hP Q hQ a b ha hb hab j ε δ
  have hp := mul_le_mul_of_nonneg_left (hP j ε δ) ha
  have hq := mul_le_mul_of_nonneg_left (hQ j ε δ) hb
  change (rowFirst j:ℝ)*((sign ε:ℝ)*(a*P.1+b*Q.1))+
    (rowSecond j:ℝ)*((sign δ:ℝ)*(a*P.2+b*Q.2))≤(rowConstant j:ℝ)
  nlinarith

theorem polygon_compact : IsCompact planePolygon :=
  isCompact_iff_compactSpace.mpr inferInstance

theorem zero_strict : (0:ℝ × ℝ)∈strictPlane := by
  intro j ε δ
  fin_cases j <;> cases ε <;> cases δ <;> norm_num [rowFirst,rowSecond,rowConstant,sign]

theorem strict_mem_interior {P : ℝ × ℝ} (hP : P∈strictPlane) : P∈interior planePolygon :=
  mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (strictPlane_open.mem_nhds hP) strictPlane_subset)

/-- The actual topological interior equals the original32 STRICT rows.
For the reverse implication, a neighborhood contains a small outward radial
extension; every literal row constant is positive. -/
theorem interior_eq_strict : interior planePolygon=strictPlane := by
  apply Set.Subset.antisymm
  · intro P hP
    have hc : Continuous (fun t : ℝ => t • P) := continuous_id.smul continuous_const
    have hn : planePolygon∈𝓝 ((1:ℝ) • P) := by
      simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hP
    have ht : {t : ℝ | t • P∈planePolygon}∈𝓝 (1:ℝ) :=
      hc.continuousAt.preimage_mem_nhds hn
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
    have hdist : (1+ε/2:ℝ)∈ball 1 ε := by
      rw [mem_ball,Real.dist_eq]
      have he : 0≤(1+ε/2:ℝ)-1 := by linarith
      rw [abs_of_nonneg he]
      linarith
    have hext := hball hdist
    intro j α β
    have hrow := hext j α β
    have hconstant : (0:ℝ)<rowConstant j := by
      fin_cases j <;> norm_num [rowConstant]
    change (rowFirst j:ℝ)*((sign α:ℝ)*((1+ε/2)*P.1))+
      (rowSecond j:ℝ)*((sign β:ℝ)*((1+ε/2)*P.2))≤(rowConstant j:ℝ) at hrow
    let L := (rowFirst j:ℝ)*((sign α:ℝ)*P.1)+
      (rowSecond j:ℝ)*((sign β:ℝ)*P.2)
    have hrow' : (1+ε/2)*L≤(rowConstant j:ℝ) := by
      dsimp [L]
      convert hrow using 1 <;> ring
    change L<(rowConstant j:ℝ)
    by_contra hnot
    have hle : (rowConstant j:ℝ)≤L := le_of_not_gt hnot
    have hL : 0<L := lt_of_lt_of_le hconstant hle
    have hmul : 0<(ε/2)*L := mul_pos (by linarith) hL
    nlinarith
  · exact strict_mem_interior

/-- A homeomorphism of the ACTUAL ambient coordinate plane carrying the
original polygon interior, polygon and frontier to the open/closed unit
ball and its sphere. Convexity, boundedness and nonempty interior are proved
for this polygon rather than supplied by the caller. -/
theorem exists_disk_normalization : ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
    h '' interior planePolygon=ball 0 1 ∧ h '' planePolygon=closedBall 0 1 ∧
      h '' frontier planePolygon=sphere 0 1 := by
  obtain ⟨h,hi,hc,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    polygon_convex ⟨0,strict_mem_interior zero_strict⟩ polygon_compact.isBounded
  exact ⟨h,hi,by simpa only [polygon_closed.closure_eq] using hc,hf⟩

@[expose] def diskNormalization : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Classical.choose exists_disk_normalization

theorem normalization_interior : diskNormalization '' interior planePolygon=ball 0 1 :=
  (Classical.choose_spec exists_disk_normalization).1

theorem normalization_polygon : diskNormalization '' planePolygon=closedBall 0 1 :=
  (Classical.choose_spec exists_disk_normalization).2.1

theorem normalization_frontier : diskNormalization '' frontier planePolygon=sphere 0 1 :=
  (Classical.choose_spec exists_disk_normalization).2.2

theorem normalization_mem (P : ℝ × ℝ) :
    P∈planePolygon ↔ diskNormalization P∈closedBall 0 1 := by
  rw [←normalization_polygon]
  constructor
  · intro hp
    exact ⟨P,hp,rfl⟩
  · rintro ⟨Q,hQ,hQP⟩
    have hQP' : Q=P := diskNormalization.injective hQP
    simpa only [hQP'] using hQ

@[expose] def polygonToClosedDisk : planePolygon ≃ₜ closedBall (0:ℝ × ℝ) 1 :=
  diskNormalization.subtype normalization_mem

@[expose] def closedDiskPolygonHomeomorph : closedBall (0:ℝ × ℝ) 1 ≃ₜ planePolygon :=
  polygonToClosedDisk.symm

theorem diskPoint_strict (z : closedBall (0:ℝ × ℝ) 1) (hz : z.val∈ball 0 1) :
    (closedDiskPolygonHomeomorph z).val∈strictPlane := by
  rw [←normalization_interior] at hz
  obtain ⟨P,hP,hPz⟩ := hz
  change diskNormalization.symm z.val∈strictPlane
  rw [←hPz,diskNormalization.symm_apply_apply,←interior_eq_strict]
  exact hP
end PELOriginalPolygonDisk318
