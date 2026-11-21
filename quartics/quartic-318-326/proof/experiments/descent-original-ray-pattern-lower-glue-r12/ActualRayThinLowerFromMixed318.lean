module
public import ActualRayThinBudgetScalars318
public import ActualRayFixedWheelWindowRate318
public import ActualRayOriginalThinWindow318
public import ActualRayPeriod16Interface318
public section
noncomputable section
namespace ActualRayThinLowerFromMixed318
open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayOccupiedLower318
open ActualRayLiteralInteriorWeight318 ActualRayInteriorMassRectangles318
open ActualSquarefreeWheelConductor16318

/-- On the actual original carrier and conductor 32R, the analytic
caller supplies only the reference mass, normalized occupancy and
the matching mixed comparison. Every old geometric/floor/strip
allowance is produced here at one eventual physical threshold. -/
theorem fixedWheel (F : Family) (y R : ℕ) (S Z ε : ℝ)
    (hy : 2 ≤ y) (hF : F.conductor = 32*R) (hR : R ∣ oddWheel y)
    (hτ1 : F.tau ≤ 1) (hρ1 : F.rho < 1)
    (hS : 0 < S) (hZ : 0 ≤ Z) (hε : 0 ≤ ε)
    (hRate : Z*(F.k:ℝ)*ε ≤ S/200)
    (hFiber : ∀ a, 0 ≤ F.fiber a ∧ F.fiber a ≤ 1)
    (hShear : |(F.K:ℝ)| * F.tau^2 ≤ 1/32)
    (hPrime : ∀ i < F.k, |((F.ci i-F.K:ℤ):ℝ)| * F.tau^2 ≤ 1/32) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (24/25:ℝ)*S ≤ partialSeries F y N →
      ((occupied F y N).card:ℝ) ≤ Z*alpha y^F.k*(wheel y:ℝ)^2 →
      (∀ r ∈ F.rows y N, MixedBudget r (ε*(r.n:ℝ)*(r.M:ℝ))) →
      S*((N:ℝ)*(cutoffT F N:ℝ))/10 ≤
        ∑ j ∈ occupied F y N, rowRaw (rowAt F y N j) := by
  have hW : 0 < wheel y := positive_wheel y
  have hα : 0 < alpha y := div_pos (by exact_mod_cast Nat.totient_pos.mpr hW)
    (by exact_mod_cast hW)
  obtain ⟨N₀,hN₀⟩ := ActualRayFixedWheelWindowRate318.eventual (wheel y) hW
    F.tau F.rho S Z F.htau hτ1 F.hrho hρ1 hS
  refine ⟨N₀,?_⟩
  intro N hN hSeries hOcc hMixed
  have hAll := hN₀ N hN
  change 2000*wheel y ≤ N ∧ 200*wheel y ≤ cutoffT F N ∧ cutoffT F N ≤ N ∧
    6400*Z*(wheel y:ℝ) ≤ S*(cutoffT F N:ℝ) ∧
    0 < N/wheel y ∧ 2*(wheel y:ℤ) < (N:ℤ) ∧
    (N:ℤ) ≤ (wheel y:ℤ)*(((N/wheel y:ℕ):ℤ)+1) ∧
    2*((wheel y:ℤ)*(⌈((N/wheel y:ℕ):ℝ)^F.rho⌉₊:ℤ)) < (N:ℤ) at hAll
  obtain ⟨hB,hT,hTN,hStrip,hn,hScale,hRight,hPower⟩ := hAll
  have hrect := ActualRayThinBudgetScalars318.sizes N (cutoffT F N) (wheel y) hW hB hT
  change (wheel y:ℝ)*((N/wheel y:ℕ):ℝ) ≤ N ∧
    (wheel y:ℝ)*(stepM F y N:ℝ) ≤ cutoffT F N ∧
    width (N/wheel y) ≤ N/wheel y ∧
    (31/250:ℝ)*(N:ℝ) ≤ (wheel y:ℝ)*(width (N/wheel y):ℝ) ∧
    (99/100:ℝ)*(cutoffT F N:ℝ) ≤ (wheel y:ℝ)*(stepM F y N:ℝ) at hrect
  obtain ⟨hnW,hmW,hI,hX,hY⟩ := hrect
  obtain ⟨hArea,hTransferError,hPeriodic⟩ :=
    ActualRayThinBudgetScalars318.allowances N (cutoffT F N) (wheel y) (width (N/wheel y))
      (stepM F y N) (N/wheel y) F.k S ε Z (alpha y^F.k)
      ((occupied F y N).card:ℝ)
      hTN hnW hmW hI hX hY hOcc (pow_nonneg hα.le _) hZ hε hRate hStrip
  have hGeom := ActualRayOriginalThinWindow318.on_occupied F y N hW
    (by omega : 16*wheel y ≤ N) hShear hPrime
  refine literal_product_log_lower F y N S ε hS hW hα hn hFiber hMixed
    hGeom hScale hRight hPower hSeries hArea hTransferError ?_
  rw [ActualRayPeriod16Interface318.actual_periodic_allowance F y N R hy hF hR]
  exact hPeriodic

end ActualRayThinLowerFromMixed318
