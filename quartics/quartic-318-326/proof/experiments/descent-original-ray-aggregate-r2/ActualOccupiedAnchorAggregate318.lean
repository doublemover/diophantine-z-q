module
public import ActualRayOccupiedLower318
public import ActualPointedPhysicalRow318
public import ActualRayAggregateLedger318
import all OriginalInteriorTelescoping318
import all ActualRayPointedAnchor318
public section
noncomputable section
namespace ActualOccupiedAnchorAggregate318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayPointedAnchor318
open ActualRayOccupiedLower318 ActualPointedPhysicalRow318
open ActualRayConditionalLower318 ActualRayLiteralInteriorWeight318
open ActualRayInteriorMassRectangles318 ActualRayConductorRows318 ActualRayPeriodicRectangle318

/-- The old row interface and the exact selected wheel digits have
the same rows. No new unit condition on the positive representative. -/
theorem row_mem_iff_occupied (H : Family) (y N : ℕ) (r : Row) :
    r∈H.rows y N ↔ ∃ z∈occupied H y N, r=rowAt H y N z := by
  classical
  constructor
  · rintro ⟨b,c,hb,hb',hc,hc',hr,hunit⟩
    have hb₀ : 0≤b-1 := by omega
    have hb₁ : ((b-1).toNat:ℤ)=b-1 := Int.toNat_of_nonneg hb₀
    have hc₁ : (c.toNat:ℤ)=c := Int.toNat_of_nonneg hc
    have hbW : (b-1).toNat<wheel y := by omega
    have hcW : c.toNat<wheel y := by omega
    let z : Digits y := (⟨(b-1).toNat,hbW⟩,⟨c.toNat,hcW⟩)
    have hargb : (z.1.val:ℤ)+1=b := by
      change ((b-1).toNat:ℤ)+1=b
      omega
    have hargc : (z.2.val:ℤ)=c := hc₁
    have heq : r=rowAt H y N z := by
      rw [rowAt,hargb,hargc]
      exact hr
    refine ⟨z,?_,heq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,heq ▸ hunit⟩
  · rintro ⟨z,hz,rfl⟩
    exact occupied_mem_actual H y N z hz

theorem rowAt_injective (H : Family) (y N : ℕ) : Function.Injective (rowAt H y N) := by
  intro z z' he
  have hb := congrArg Row.b he
  have hc := congrArg Row.c he
  change (z.1.val:ℤ)+1=(z'.1.val:ℤ)+1 at hb
  change (z.2.val:ℤ)=(z'.2.val:ℤ) at hc
  apply Prod.ext
  · apply Fin.ext
    have h : (z.1.val:ℤ)=(z'.1.val:ℤ) := by omega
    exact_mod_cast h
  · apply Fin.ext
    exact_mod_cast hc

/-- Explicit positivity witness for the public row header. Its proof may
unfold the old private-imported `Family.row` without exporting its body. -/
theorem rowAt_pos (H : Family) (y N : ℕ) (z : Digits y)
    (hn : 0<N/wheel y) : 0<(rowAt H y N z).n := by
  change 0<N/wheel y
  exact hn

/-- Literal normalization of the old per-row certificate, where
the supplied estimates need only be stated on occupied wheel digits. -/
theorem mixed_rows_of_occupied_anchors (H : Family) (y N : ℕ)
    (hn : 0<N/wheel y) (eps : ℝ)
    (h : ∀ z∈occupied H y N, AnchorBudget (rowAt H y N z) (rowAt_pos H y N z hn) eps) :
    ∀ r∈H.rows y N, MixedBudget r (eps*((r.n:ℝ)*(r.M:ℝ))) := by
  intro r hr
  obtain ⟨z,hz,rfl⟩ := (row_mem_iff_occupied H y N r).mp hr
  exact mixed_of_anchor _ (rowAt_pos H y N z hn) eps (h z hz)

/-- Each DIGIT in the literal occupied set appears precisely once;
no summation over Gaussian lifts, signs or all y≤Y. -/
def anchoredDefect (H : Family) (y N : ℕ) (hn : 0<N/wheel y) : ℝ :=
  ∑ z∈occupied H y N,
    let r := rowAt H y N z
    ∑ j∈Finset.range H.k, correlation r (rowAt_pos H y N z hn) j (center r j)

theorem occupied_anchor_absolute (H : Family) (y N : ℕ)
    (hn : 0<N/wheel y) (eps : ℝ)
    (h : ∀ z∈occupied H y N, AnchorBudget (rowAt H y N z) (rowAt_pos H y N z hn) eps) :
    |anchoredDefect H y N hn|≤((occupied H y N).card:ℝ)*
      ((H.k:ℝ)*(eps*((N/wheel y:ℕ):ℝ)*(stepM H y N:ℝ))) := by
  unfold anchoredDefect
  calc
    _ ≤ ∑ z∈occupied H y N,
      |∑ j∈Finset.range H.k, correlation (rowAt H y N z) (rowAt_pos H y N z hn) j (center (rowAt H y N z) j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z∈occupied H y N,
      (H.k:ℝ)*(eps*((N/wheel y:ℕ):ℝ)*(stepM H y N:ℝ)) := by
      apply Finset.sum_le_sum
      intro z hz
      let r := rowAt H y N z
      calc
        _ ≤ ∑ j∈Finset.range H.k, |correlation r (rowAt_pos H y N z hn) j (center r j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j∈Finset.range H.k, eps*((N/wheel y:ℕ):ℝ)*(stepM H y N:ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hh := h z hz j (Finset.mem_range.mp hj)
          simpa only [mul_assoc] using hh
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_range]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

def rawTotal (H : Family) (y N : ℕ) : ℝ :=
  ∑ z∈occupied H y N, rowRaw (rowAt H y N z)

theorem rawTotal_eval (H : Family) (y N : ℕ) :
    rawTotal H y N = ∑ z∈occupied H y N, rowRaw (rowAt H y N z) := rfl

def meanTotal (H : Family) (y N : ℕ) : ℝ :=
  (width (N/wheel y):ℝ)*(stepM H y N:ℝ)*∑ z∈occupied H y N,residueMeanAt H y N z

/-- Periodic sample sum, BEFORE replacing it with the one-block
reference. It uses the original physical table entries. -/
def foldedRow (H : Family) (y N : ℕ) (z : Digits y) : ℝ :=
  let r := rowAt H y N z
  rectangle (fold (table H.conductor r.k (d r) H.fiber) H.conductor r.W
    (z.1.val+1) z.2.val) (start r.n) 1 (width r.n) r.M

def foldedTotal (H : Family) (y N : ℕ) : ℝ :=
  ∑ z∈occupied H y N, foldedRow H y N z

def stripCost (H : Family) (y N : ℕ) : ℝ :=
  ((((wheel y).lcm H.conductor/wheel y:ℕ):ℝ))*
    ((width (N/wheel y):ℝ)+(stepM H y N:ℝ))

theorem aggregate_identity (H : Family) (y N : ℕ) (hn : 0<N/wheel y)
    (hW : 0<wheel y)
    (hBox : ∀ z∈occupied H y N, ∀ t : Dom (rowAt H y N z),
      dummy (rowAt H y N z) t=1 →
      InThinBox (rowAt H y N z) N (cutoffT H N)
        (baseIndex (rowAt H y N z) t) (stepIndex (rowAt H y N z) t))
    (hScale : 2*(wheel y:ℤ)<(N:ℤ))
    (hRight : (N:ℤ)≤(wheel y:ℤ)*(((N/wheel y:ℕ):ℤ)+1))
    (hPower : 2*((wheel y:ℤ)*(⌈(((N/wheel y:ℕ):ℝ))^H.rho⌉₊:ℤ))<(N:ℤ)) :
    alpha y^H.k * rawTotal H y N - foldedTotal H y N = anchoredDefect H y N hn := by
  rw [rawTotal,foldedTotal,anchoredDefect,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  let r := rowAt H y N z
  have hClean (t : Dom r) (ht : dummy r t=1) (i : ℕ) (hi : i<r.k) :
      noWrap r i t ∧ (r.cut:ℤ)≤baseIndex r t+shift r i (stepIndex r t) := by
    obtain ⟨h₀,h₁,h₂⟩ := physical_box_passes_row_window r N (cutoffT H N) t
      (hBox z hz t ht) hScale hRight hPower i hi
    exact output_window_implies_no_wrap r i t hW h₀ h₁ h₂
  have hb : r.b=((z.1.val+1:ℕ):ℤ) := by
    change (z.1.val:ℤ)+1=((z.1.val+1:ℕ):ℤ)
    push_cast <;> rfl
  exact actual_signed_row_identity r (rowAt_pos H y N z hn) H.conductor (z.1.val+1) z.2.val H.fiber
    hb rfl (fun _ => rfl) (fun t ht i hi => (hClean t ht i hi).1)
    (fun t ht i hi => (hClean t ht i hi).2)

theorem aggregate_periodic_error (H : Family) (y N : ℕ)
    (hW : 0<wheel y) (hFiber : ∀ a,0≤H.fiber a ∧ H.fiber a≤1) :
    |foldedTotal H y N - meanTotal H y N| ≤ ((occupied H y N).card:ℝ)*stripCost H y N := by
  rw [foldedTotal,meanTotal,Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z∈occupied H y N, |foldedRow H y N z-
        (width (N/wheel y):ℝ)*(stepM H y N:ℝ)*residueMeanAt H y N z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z∈occupied H y N, stripCost H y N := by
      apply Finset.sum_le_sum
      intro z _
      let r := rowAt H y N z
      have h := fixed_conductor_row_error (table H.conductor r.k (d r) H.fiber)
        H.conductor r.W (z.1.val+1) z.2.val hW H.hconductor
        (start r.n) 1 (width r.n) r.M 1
        (table_bounds H.conductor r.k (d r) H.fiber hFiber)
      simpa only [foldedRow,residueMeanAt,rowMean,stripCost,r,mul_one] using h
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- Exact aggregate transport in the absolute direction, useful for
the unchanged mixed comparison certificate. -/
theorem absolute_mixed_error (H : Family) (y N : ℕ) (hn : 0<N/wheel y) (D P : ℝ)
    (heq : alpha y^H.k * rawTotal H y N - foldedTotal H y N = anchoredDefect H y N hn)
    (hD : |anchoredDefect H y N hn|≤D)
    (hP : |foldedTotal H y N-meanTotal H y N|≤P) :
    |alpha y^H.k*rawTotal H y N-meanTotal H y N|≤D+P := by
  calc
    _ = |anchoredDefect H y N hn+(foldedTotal H y N-meanTotal H y N)| := by
      rw [←heq]
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hD hP)

/-- Same 24/25, 3/25 and two independent 1/200 allowances;
one signed bound on the sum of ACTUAL occupied row tests suffices. -/
theorem lower_of_aggregate_signed (H : Family) (y N : ℕ) (hn : 0<N/wheel y)
    (S D : ℝ) (hS : 0<S) (hW : 0<wheel y) (hα : 0<alpha y)
    (hFiber : ∀ a,0≤H.fiber a ∧ H.fiber a≤1)
    (heq : alpha y^H.k * rawTotal H y N - foldedTotal H y N = anchoredDefect H y N hn)
    (hD : -D≤anchoredDefect H y N hn)
    (hSeries : (24/25:ℝ)*S≤partialSeries H y N)
    (hArea : (3/25:ℝ)*((N:ℝ)*(cutoffT H N:ℝ))≤
      (width (N/wheel y):ℝ)*(stepM H y N:ℝ)*(wheel y:ℝ)^2)
    (hTransfer : D≤alpha y^H.k*(S*((N:ℝ)*(cutoffT H N:ℝ)))/200)
    (hPeriodic : ((occupied H y N).card:ℝ)*stripCost H y N≤
      alpha y^H.k*(S*((N:ℝ)*(cutoffT H N:ℝ)))/200) :
    S*((N:ℝ)*(cutoffT H N:ℝ))/10≤rawTotal H y N := by
  have hp := (abs_le.mp (aggregate_periodic_error H y N hW hFiber)).1
  have hs : -(D+((occupied H y N).card:ℝ)*stripCost H y N)≤
      alpha y^H.k*rawTotal H y N-meanTotal H y N := by
    rw [←heq] at hD
    linarith only [hD,hp]
  exact ActualRayAggregateLedger318.lower_of_signed_total (alpha y) S (rawTotal H y N)
    (∑ z∈occupied H y N,residueMeanAt H y N z) H.k (wheel y)
    (width (N/wheel y)) (stepM H y N) N (cutoffT H N) hα hS hW hSeries hArea
    D (((occupied H y N).card:ℝ)*stripCost H y N) hTransfer hPeriodic hs

end ActualOccupiedAnchorAggregate318
