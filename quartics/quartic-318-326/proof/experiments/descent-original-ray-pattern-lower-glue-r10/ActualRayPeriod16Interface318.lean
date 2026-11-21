module
public import ActualSquarefreeWheelConductor16318
public import ActualRayCubePeriod16318
public import ActualRayOccupiedLower318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayPeriod16Interface318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayOccupiedLower318
open ActualRayConditionalLower318 ActualRayInteriorMassRectangles318
open ActualRayConductorRows318 ActualRayPeriodicRectangle318
open ActualRayLiteralInteriorWeight318 ActualSquarefreeWheelConductor16318

/-- Pure normalization of the ORIGINAL Family.partialSeries; no new
finite field rate, ray replacement, or dummy condition is used. -/
theorem original_series_at_16 (H : Family) (y N R : ℕ)
    (hy : 2≤y) (hF : H.conductor=32*R) (hR : R∣oddWheel y) :
    let W := wheel y
    let e := digits W 16 (positive_wheel y)
    partialSeries H y N =
      (∑ U : Fin (W*16),∑ V : Fin (W*16),
        unitMask H y N (e.symm U).1 (e.symm V).1*
        table H.conductor H.k (fun i => H.ci i-H.K) H.fiber
          ((U.val+1)%H.conductor) (V.val%H.conductor))/
        (alpha y^H.k*((W*16:ℕ):ℝ)^2) := by
  have h16 : (wheel y).lcm H.conductor/wheel y=16 := by
    rw [hF]
    exact wheel_period_16 hy hR
  let W := wheel y
  let main (E : ℕ) : ℝ :=
    let e := digits W E (positive_wheel y)
    (∑ U : Fin (W*E),∑ V : Fin (W*E),
      unitMask H y N (e.symm U).1 (e.symm V).1 *
      table H.conductor H.k (fun i => H.ci i-H.K) H.fiber
        ((U.val+1)%H.conductor) (V.val%H.conductor)) /
      (alpha y^H.k*((W*E:ℕ):ℝ)^2)
  have hMain : partialSeries H y N=main (W.lcm H.conductor/W) :=
    partialSeries_physical H y N (positive_wheel y)
  change partialSeries H y N=main 16
  exact hMain.trans (congrArg main h16)

theorem actual_periodic_allowance (H : Family) (y N R : ℕ)
    (hy : 2≤y) (hF : H.conductor=32*R) (hR : R∣oddWheel y) :
    ((occupied H y N).card:ℝ)*
      ((((wheel y).lcm H.conductor/wheel y:ℕ):ℝ)*
        ((width (N/wheel y):ℝ)+(stepM H y N:ℝ))) =
    16*((occupied H y N).card:ℝ)*((width (N/wheel y):ℝ)+(stepM H y N:ℝ)) := by
  rw [hF,wheel_period_16 hy hR]
  push_cast <;> ring

/-- The actual conditional selector density is supported at rational
norm 17 mod32, not just odd norm. This is a property of the specified
reference ray, as shown by the separate arithmetic conductor leaf. -/
def DyadicSupport (μ : ℤ→ℝ) : Prop :=
  ∀ b,b%32≠17→μ b=0

theorem dyadic_support_passes_modulus (F : ℕ) (hF : 32∣F) (μ : ℤ→ℝ)
    (hμ : DyadicSupport μ) (p : ℤ) (hp : p%32≠17) : μ (p%(F:ℤ))=0 := by
  have h : p%(F:ℤ)≡p [ZMOD (F:ℤ)] := by
    change (p%(F:ℤ))%(F:ℤ)=p%(F:ℤ)
    rw [Int.emod_emod]
  have hDiv : (32:ℤ)∣(F:ℤ) := by exact_mod_cast hF
  have hd := Int.ModEq.of_dvd hDiv h
  change (p%(F:ℤ))%32=p%32 at hd
  apply hμ
  rwa [hd]

theorem actual_table_zero_off_dyadic (H : Family) (R U V : ℕ)
    (hF : H.conductor=32*R) (hμ : DyadicSupport H.fiber)
    (fails : ∃ i<H.k,((U:ℤ)+(H.ci i-H.K)*(V:ℤ)^2)%32≠17) :
    table H.conductor H.k (fun i => H.ci i-H.K) H.fiber U V=0 := by
  obtain ⟨i,hi,hh⟩ := fails
  have hDiv : 32∣H.conductor := ⟨R,hF⟩
  unfold table
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    (dyadic_support_passes_modulus _ hDiv _ hμ _ hh)

def RayDyadic (ray : ℕ→Prop) : Prop := ∀ p,ray p→p%32=17

theorem log_prime_zero_off_dyadic (ray : ℕ→Prop) (hr : RayDyadic ray) (p : ℤ)
    (hp : p%32≠17) : logPrimeRay ray p=0 := by
  unfold logPrimeRay
  apply if_neg
  intro h
  have hNat := hr _ h.2.2
  have hInt : ((p.natAbs:ℤ)%32:ℤ)=17 := by
    change ((p.natAbs:ℤ)%((32:ℕ):ℤ))=((17:ℕ):ℤ)
    rw [Int.ofNat_mod_ofNat,hNat]
  rw [Int.natCast_natAbs,abs_of_pos h.1] at hInt
  exact hp hInt

/-- Both the genuine prime and its conditional mean vanish off the
same physical norm residue, so the EXISTING centered cube is
supported in the one residue cell of surviving_cell_unique. -/
theorem actual_centeredAt_zero_off_dyadic (r : Row) (F : ℕ) (hF : 32∣F)
    (hr : RayDyadic r.ray) (μ : ℤ→ℝ) (hμ : DyadicSupport μ)
    (hPeriodic : ∀ z,r.mu z=μ (z%(F:ℤ))) (i : ℕ) (x : ℤ)
    (hp : ((r.W:ℤ)*rep r.n x+residue r i)%32≠17) : centeredAt r i x=0 := by
  let p := (r.W:ℤ)*rep r.n x+residue r i
  have hf : logPrimeRay r.ray p=0 := log_prime_zero_off_dyadic r.ray hr p hp
  have hm : r.mu p=0 := (hPeriodic p).trans (dyadic_support_passes_modulus F hF μ hμ p hp)
  change (if (r.cut:ℤ)≤rep r.n x then r.phiRatio*logPrimeRay r.ray p else 0)-r.mu p=0
  simp [hf,hm]

/-- Fixed s, field and genuine Family. This is solely the centered
AFFINE cube estimate on the actual chosen common cutoff schedule. -/
def LinearOnDiagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta : ℝ) : Prop :=
  ∃ N₀ : ℕ,∀ N≥N₀,∀ r∈H.rows (Y N) N,
    LinearBudget r a (qMax (Y N)) (jMin (Y N) N) (jMax (Y N) N) delta

/-- The distinct pointed nonlinear donor, conditional on those exact
linear cubes, on the SAME selected schedule. No fixed-y continuation
and no full asymptotic in u,v is requested. -/
def PointedTransferOnDiagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta eps : ℝ) : Prop :=
  ∃ N₀ : ℕ,∀ N≥N₀,∀ r∈H.rows (Y N) N,
    LinearBudget r a (qMax (Y N)) (jMin (Y N) N) (jMax (Y N) N) delta →
    MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ))

theorem actual_mixed_on_common_diagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (delta eps : ℝ)
    (linear : LinearOnDiagonal H Y a qMax jMin jMax delta)
    (transfer : PointedTransferOnDiagonal H Y a qMax jMin jMax delta eps) :
    ∃ N₀ : ℕ,∀ N≥N₀,∀ r∈H.rows (Y N) N,
      MixedBudget r (eps*(r.n:ℝ)*(r.M:ℝ)) := by
  obtain ⟨Nl,hl⟩ := linear
  obtain ⟨Np,hp⟩ := transfer
  refine ⟨max Nl Np,?_⟩
  intro N hN r hr
  exact hp N ((le_max_right _ _).trans hN) r hr
    (hl N ((le_max_left _ _).trans hN) r hr)

end ActualRayPeriod16Interface318
