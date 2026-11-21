module
public import ActualRayLiteralInteriorWeight318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayInteriorMassRectangles318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayLiteralInteriorWeight318
open ActualRayPeriodicRectangle318 ActualRayConductorRows318

@[expose] def start (n : ℕ) : ℕ := (5*n+7)/8
@[expose] def width (n : ℕ) : ℕ := (3*n)/4+1-start n

theorem interior_span (n : ℕ) (hn : 0 < n) :
    1 ≤ start n ∧ start n-1+width n ≤ n := by
  simp only [width,start]
  omega

theorem interior_test (n i : ℕ) (hn : 0 < n) :
    (5*n ≤ 8*(i+1) ∧ 4*(i+1) ≤ 3*n) ↔
    start n ≤ i+1 ∧ i+1 < start n+width n := by
  simp only [width,start]
  omega

theorem select_line (G : ℕ → ℝ) (n a l : ℕ) (ha : 1 ≤ a) (hl : a-1+l ≤ n) :
    (∑ i ∈ Finset.range n, if a ≤ i+1 ∧ i+1 < a+l then G (i+1) else 0) =
    line G a l := by
  let q := a-1
  let t := n-(q+l)
  let H (i : ℕ) := if a ≤ i+1 ∧ i+1 < a+l then G (i+1) else 0
  have hq : q+1=a := by unfold q; omega
  have hN : n=q+l+t := by unfold t q; omega
  have hPre : (∑ i ∈ Finset.range q, H i)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hii := Finset.mem_range.mp hi
    exact if_neg (by omega)
  have hPost : (∑ i ∈ Finset.range t, H (q+l+i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (by omega)
  have hMid : (∑ i ∈ Finset.range l, H (q+i))=line G a l := by
    unfold line
    apply Finset.sum_congr rfl
    intro i hi
    have hii := Finset.mem_range.mp hi
    have hm : a ≤ q+i+1 ∧ q+i+1 < a+l := by omega
    have he : q+i+1=a+i := by omega
    simp only [H,if_pos hm,he]
  change (∑ i ∈ Finset.range n, H i)=_
  calc
    _=∑ i ∈ Finset.range (q+l+t), H i := congrArg (fun N => ∑ i ∈ Finset.range N, H i) hN
    _=(∑ i ∈ Finset.range q, H i)+(∑ i ∈ Finset.range l, H (q+i))+
        ∑ i ∈ Finset.range t, H (q+l+i) := by
      rw [Finset.sum_range_add H (q+l) t,Finset.sum_range_add H q l]
    _=_ := by rw [hPre,hMid,hPost,zero_add,add_zero]

/-- Restrict to the existing interior dummy, not a redefined window.
The coarse step starts at 1 and is not clipped to the base length. -/
theorem mass_rectangle (r : Row) (hn : 0 < r.n) (g : Dom r → ℝ) (G : ℕ → ℕ → ℝ)
    (h : ∀ z, dummy r z=1 → g z=G (z.1.val+1) (z.2.val+1)) :
    mass r g=rectangle G (start r.n) 1 (width r.n) r.M := by
  have hPoint (z : Dom r) :
      dummy r z*g z=if start r.n ≤ z.1.val+1 ∧ z.1.val+1 < start r.n+width r.n
        then G (z.1.val+1) (z.2.val+1) else 0 := by
    by_cases hv : start r.n ≤ z.1.val+1 ∧ z.1.val+1 < start r.n+width r.n
    · have hd : dummy r z=1 := by
        rw [dummy,if_pos ((interior_test r.n z.1.val hn).mpr hv)]
      rw [hd,one_mul,if_pos hv,h z hd]
    · have hd : dummy r z=0 := by
        rw [dummy,if_neg (fun he => hv ((interior_test r.n z.1.val hn).mp he))]
      simp only [hd,zero_mul,if_neg hv]
  unfold mass
  simp_rw [hPoint,Fintype.sum_prod_type,Fin.sum_univ_eq_sum_range]
  have hInner (i : ℕ) :
      (∑ m ∈ Finset.range r.M, if start r.n ≤ i+1 ∧ i+1 < start r.n+width r.n
        then G (i+1) (m+1) else 0) =
        if start r.n ≤ i+1 ∧ i+1 < start r.n+width r.n then line (G (i+1)) 1 r.M else 0 := by
    by_cases hI : start r.n ≤ i+1 ∧ i+1 < start r.n+width r.n
    · simp only [if_pos hI,line,Nat.add_comm 1]
    · simp [hI]
  simp_rw [hInner]
  exact select_line (fun i => line (G i) 1 r.M) r.n (start r.n) (width r.n)
    (interior_span r.n hn).1 (interior_span r.n hn).2

theorem mean_mass_exact (r : Row) (hn : 0 < r.n) (F b c : ℕ) (μ : ℤ → ℝ)
    (hb : r.b=(b:ℤ)) (hc : r.c=(c:ℤ)) (hμ : ∀ a, r.mu a=μ (a%(F:ℤ)))
    (hwrap : ∀ z, dummy r z=1 → ∀ i < r.k, noWrap r i z) :
    mass r (fun z => ∏ i∈Finset.range r.k, OriginalInteriorTelescoping318.mean r i z)=
      rectangle (fold (table F r.k (d r) μ) F r.W b c)
        (start r.n) 1 (width r.n) r.M := by
  apply mass_rectangle r hn
  intro z hz
  rw [actual_fold]
  unfold table
  apply Finset.prod_congr rfl
  intro i hi
  have hU : physicalU r (baseIndex r z)=((b+r.W*(z.1.val+1):ℕ):ℤ) := by
    simp only [physicalU,baseIndex,hb,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    ring
  have hV : physicalV r (stepIndex r z)=((c+r.W*(z.2.val+1):ℕ):ℤ) := by
    simp only [physicalV,stepIndex,hc,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    ring
  rw [OriginalInteriorTelescoping318.mean,hμ,
    output_exact r i z (hwrap z hz i (Finset.mem_range.mp hi)),physical_shear,hU,hV]

@[expose] def rawWeight (r : Row) (x m : ℕ) : ℝ :=
  ∏ i∈Finset.range r.k, logPrimeRay r.ray (physicalPrime r i (x:ℤ) (m:ℤ))

theorem rectangle_scale (G : ℕ → ℕ → ℝ) (a z n M : ℕ) (u : ℝ) :
    rectangle (fun x m => u*G x m) a z n M=u*rectangle G a z n M := by
  simp only [rectangle,line_scale]

theorem prime_mass_exact (r : Row) (hn : 0 < r.n)
    (hwrap : ∀ z, dummy r z=1 → ∀ i < r.k, noWrap r i z)
    (hcut : ∀ z, dummy r z=1 → ∀ i < r.k,
      (r.cut:ℤ) ≤ baseIndex r z+shift r i (stepIndex r z)) :
    mass r (fun z => ∏ i∈Finset.range r.k, f r i z)=
      r.phiRatio^r.k*rectangle (rawWeight r) (start r.n) 1 (width r.n) r.M := by
  rw [←rectangle_scale]
  apply mass_rectangle r hn
  intro z hz
  simpa only [rawWeight,baseIndex,stepIndex,Nat.cast_add,Nat.cast_one] using
    prime_product_exact r z (hwrap z hz) (hcut z hz)

end ActualRayInteriorMassRectangles318
