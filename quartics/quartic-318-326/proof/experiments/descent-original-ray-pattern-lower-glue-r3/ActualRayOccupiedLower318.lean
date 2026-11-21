module
public import ActualRayConditionalLower318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayOccupiedLower318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayLiteralInteriorWeight318
open ActualRayInteriorMassRectangles318 ActualRayConditionalLower318
open ActualRayPeriodicRectangle318 ActualRayConductorRows318

abbrev Digits (y : ℕ) := Fin (wheel y) × Fin (wheel y)

@[expose] def rowAt (H : Family) (y N : ℕ) (z : Digits y) : Row :=
  H.row y N ((z.1.val:ℤ)+1) (z.2.val:ℤ)

@[expose] def occupied (H : Family) (y N : ℕ) : Finset (Digits y) := by
  classical
  exact Finset.univ.filter fun z => ∀ i<H.k, Nat.Coprime
    (residue (rowAt H y N z) i).natAbs (wheel y)

theorem occupied_mem_actual (H : Family) (y N : ℕ) (z : Digits y)
    (hz : z∈occupied H y N) : rowAt H y N z∈H.rows y N := by
  classical
  have hres : ∀ i<H.k, Nat.Coprime (residue (rowAt H y N z) i).natAbs (wheel y) :=
    (Finset.mem_filter.mp hz).2
  have hbN := Nat.succ_le_of_lt z.1.isLt
  have hb : (z.1.val:ℤ)+1≤(wheel y:ℤ) := by exact_mod_cast hbN
  have hc : (z.2.val:ℤ)<(wheel y:ℤ) := by exact_mod_cast z.2.isLt
  change ∃ b c : ℤ, 1≤b ∧ b≤(wheel y:ℤ) ∧ 0≤c ∧ c<(wheel y:ℤ) ∧
    rowAt H y N z=H.row y N b c ∧ _
  exact ⟨_,_,by positivity,hb,by positivity,hc,rfl,hres⟩

@[expose] def cutoffT (H : Family) (N : ℕ) : ℕ := ⌊H.tau*Real.sqrt (N:ℝ)⌋₊
@[expose] def stepM (H : Family) (y N : ℕ) : ℕ := cutoffT H N / wheel y - 1
@[expose] def alpha (y : ℕ) : ℝ := (Nat.totient (wheel y):ℝ)/(wheel y:ℝ)
@[expose] def residueMeanAt (H : Family) (y N : ℕ) (z : Digits y) : ℝ :=
  rowMean (rowAt H y N z) H.conductor (z.1.val+1) z.2.val H.fiber

/-- The exact padded singular coefficient: all compatible rows,
one E×E conductor mean on each; W² compensates the row indexing,
and alpha^k is the same normalization used in the prime moment. -/
@[expose] def partialSeries (H : Family) (y N : ℕ) : ℝ :=
  (∑ z∈occupied H y N, residueMeanAt H y N z)/(alpha y^H.k*(wheel y:ℝ)^2)

def unitMask (H : Family) (y N : ℕ) (b c : Fin (wheel y)) : ℝ := by
  classical
  exact if (b,c)∈occupied H y N then 1 else 0

/-- Exact mass of the same CRT mask on the physical conductor grid;
positive U representatives are 1 through W*E, step representatives
are 0 through W*E−1. There is no unit condition on the dummy. -/
theorem partialSeries_physical (H : Family) (y N : ℕ) (hW : 0<wheel y) :
    let W := wheel y
    let E := W.lcm H.conductor/W
    let e := digits W E hW
    partialSeries H y N =
      (∑ U : Fin (W*E), ∑ V : Fin (W*E),
        unitMask H y N (e.symm U).1 (e.symm V).1 *
        table H.conductor H.k (fun i => H.ci i-H.K) H.fiber
          ((U.val+1)%H.conductor) (V.val%H.conductor))/
        (alpha y^H.k*((W*E:ℕ):ℝ)^2) := by
  classical
  let W := wheel y
  let E := W.lcm H.conductor/W
  let G := table H.conductor H.k (fun i => H.ci i-H.K) H.fiber
  let K := unitMask H y N
  have hMask :
      (∑ j∈occupied H y N, residueMeanAt H y N j) =
        ∑ j : Digits y, K j.1 j.2*residueMeanAt H y N j := by
    unfold occupied
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ∀ i<H.k, Nat.Coprime (residue (rowAt H y N j) i).natAbs (wheel y)
    · simp [K,unitMask,occupied,hj]
    · simp [K,unitMask,occupied,hj]
  have hBlock :
      (∑ j : Digits y, K j.1 j.2*residueMeanAt H y N j) =
      (∑ b : Fin W, ∑ c : Fin W, K b c*
        rectangle (fold G H.conductor W (b.val+1) c.val) 0 0 E E)/(E:ℝ)^2 := by
    simp only [Fintype.sum_prod_type,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    change K b c * (rectangle (fold G H.conductor W (b.val+1) c.val) 0 0 E E / (E:ℝ)^2) = _
    rw [mul_div_assoc]
  let e := digits W E hW
  change partialSeries H y N =
    (∑ U : Fin (W*E), ∑ V : Fin (W*E),
      K (e.symm U).1 (e.symm V).1*G ((U.val+1)%H.conductor) (V.val%H.conductor)) /
      (alpha y^H.k*((W*E:ℕ):ℝ)^2)
  rw [partialSeries,hMask,hBlock,folded_block_sum G H.conductor W E hW K,div_div]
  congr 1
  change (E:ℝ)^2*(alpha y^H.k*(W:ℝ)^2) = _
  push_cast
  ring

@[expose] def InThinBox (r : Row) (N T : ℕ) (x m : ℤ) : Prop :=
  let u := physicalUOriginal r x m
  let v := physicalV r m
  (N:ℤ)≤2*u ∧ u≤(N:ℤ) ∧ 1≤v ∧ v≤(T:ℤ) ∧
  ∀ i<r.k, (N:ℤ)≤2*physicalPrime r i x m ∧ physicalPrime r i x m≤(N:ℤ)

theorem physical_box_passes_row_window (r : Row) (N T : ℕ) (z : Dom r)
    (hgeom : InThinBox r N T (baseIndex r z) (stepIndex r z))
    (hScale : 2*(r.W:ℤ)<(N:ℤ))
    (hRight : (N:ℤ)≤(r.W:ℤ)*((r.n:ℤ)+1))
    (hPower : 2*((r.W:ℤ)*(r.cut:ℤ))<(N:ℤ)) (i : ℕ) (hi : i<r.k) :
    let p := physicalPrime r i (baseIndex r z) (stepIndex r z)
    (r.W:ℤ)<p ∧ p≤(r.W:ℤ)*((r.n:ℤ)+1) ∧ (r.W:ℤ)*(r.cut:ℤ)<p := by
  have hp := hgeom.2.2.2.2 i hi
  exact ⟨by omega,hp.2.trans hRight,by omega⟩

/-- Explicit conditional positive genuine prime-log mass on the same
original thin carrier. The per-row transfer is an actual MixedBudget
on the prescribed H.rows; only the finite normalizations are proved
here. The optional ray-to-Gaussian witnesses do not inflate this weight. -/
theorem literal_product_log_lower (H : Family) (y N : ℕ) (Ss eps : ℝ)
    (hSs : 0<Ss) (hW : 0<wheel y) (hα : 0<alpha y) (hn : 0<N/wheel y)
    (hFiber : ∀ a, 0≤H.fiber a ∧ H.fiber a≤1)
    (hTransfer : ∀ r∈H.rows y N, MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ)))
    (hBox : ∀ j∈occupied H y N, ∀ z : Dom (rowAt H y N j),
      dummy (rowAt H y N j) z=1 →
      InThinBox (rowAt H y N j) N (cutoffT H N)
        (baseIndex (rowAt H y N j) z) (stepIndex (rowAt H y N j) z))
    (hScale : 2*(wheel y:ℤ)<(N:ℤ))
    (hRight : (N:ℤ)≤(wheel y:ℤ)*(((N/wheel y:ℕ):ℤ)+1))
    (hPower : 2*((wheel y:ℤ)*(⌈(((N/wheel y:ℕ):ℝ))^H.rho⌉₊:ℤ))<(N:ℤ))
    (hSeries : (24/25:ℝ)*Ss≤partialSeries H y N)
    (hArea : (3/25:ℝ)*((N:ℝ)*(cutoffT H N:ℝ))≤
      (width (N/wheel y):ℝ)*(stepM H y N:ℝ)*(wheel y:ℝ)^2)
    (hTransferError : ((occupied H y N).card:ℝ)*((H.k:ℝ)*
        (eps*((N/wheel y:ℕ):ℝ)*(stepM H y N:ℝ)))≤
      alpha y^H.k*(Ss*((N:ℝ)*(cutoffT H N:ℝ)))/200)
    (hPeriodicError : ((occupied H y N).card:ℝ)*
        (((((wheel y).lcm H.conductor/wheel y:ℕ):ℝ))*
          ((width (N/wheel y):ℝ)+(stepM H y N:ℝ)))≤
      alpha y^H.k*(Ss*((N:ℝ)*(cutoffT H N:ℝ)))/200) :
    Ss*((N:ℝ)*(cutoffT H N:ℝ))/10≤∑ j∈occupied H y N, rowRaw (rowAt H y N j) := by
  refine finite_lower (occupied H y N) (fun j => rowRaw (rowAt H y N j))
    (residueMeanAt H y N) (alpha y) hα H.k (wheel y) hW
    (width (N/wheel y)) (stepM H y N) N (cutoffT H N) Ss hSs
    ((H.k:ℝ)*(eps*((N/wheel y:ℕ):ℝ)*(stepM H y N:ℝ)))
    ((((wheel y).lcm H.conductor/wheel y:ℕ):ℝ)*
      ((width (N/wheel y):ℝ)+(stepM H y N:ℝ)))
    ?_ hSeries hArea hTransferError hPeriodicError
  intro j hj
  let r := rowAt H y N j
  have hPoint (z : Dom r) (hz : dummy r z=1) (i : ℕ) (hi : i<r.k) :=
    physical_box_passes_row_window r N (cutoffT H N) z (hBox j hj z hz)
      hScale hRight hPower i hi
  have hGood (z : Dom r) (hz : dummy r z=1) (i : ℕ) (hi : i<r.k) :
      noWrap r i z ∧ (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z) := by
    obtain ⟨h₁,h₂,h₃⟩ := hPoint z hz i hi
    exact output_window_implies_no_wrap r i z hW h₁ h₂ h₃
  have hb : r.b=((j.1.val+1:ℕ):ℤ) := by
    change (j.1.val:ℤ)+1=((j.1.val+1:ℕ):ℤ)
    push_cast <;> rfl
  exact actual_row_error r hn H.conductor (j.1.val+1) j.2.val
    hW H.hconductor H.fiber hFiber hb rfl (fun _ => rfl)
    (fun z hz i hi => (hGood z hz i hi).1)
    (fun z hz i hi => (hGood z hz i hi).2) eps
    (hTransfer r (occupied_mem_actual H y N j hj))

end ActualRayOccupiedLower318
