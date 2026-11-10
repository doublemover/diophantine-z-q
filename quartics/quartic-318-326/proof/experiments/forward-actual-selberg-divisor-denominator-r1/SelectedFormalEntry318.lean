module
public import SelectedPoleFullSource318
public section
noncomputable section
namespace SelectedFormalEntry318
open ConcreteG8Domain (K D)
open GlobalGeneratorPoints318 (R)
open CoherentMultipleCharts318 (chartU chartV)
open ValuativeOrbitBounds318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- The exact reduction-order input needed at a selected split prime: the
specified multiple of the ORIGINAL HALF POINT lies in the actual formal
subgroup. This is not membership for P=2R and not a caller-chosen chart. -/
@[expose] def Entry (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) : Prop :=
  ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom D
    ((M:ℤ) • R) ∈
  AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue ℚ_[p])
    (ActualSplitOrbitEntry318.nonarchimedean p)
    (ConcretePadic318.embedding p rho hr D) (ActualSplitOrbitEntry318.coefficient_integral p rho hr)

lemma near (rho : ℚ_[p]) (hr : rho^2=2) (M : ℕ) (hM : Entry p rho hr M) :
    Near (ConcretePadic318.place p rho hr) 1 (chartU (M:ℤ)) (chartV (M:ℤ)) := by
  obtain ⟨hu,hv⟩ := FormalPoleCoherentChart318.actual_chart
    (ConcretePadic318.embedding p rho hr).toRingHom
    (NormedField.toAbsoluteValue ℚ_[p]) (ActualSplitOrbitEntry318.nonarchimedean p)
    (ActualSplitOrbitEntry318.coefficient_integral p rho hr) ((M:ℤ) • R) hM
  exact ⟨ActualSplitOrbitEntry318.positive_depth p _ hu,
    ActualSplitOrbitEntry318.positive_depth p _ hv⟩

/-- The original primary exponent3 actually gives oriented depth4, uniformly
for every signed root label at the same CRT index. -/
theorem primary (rho : ℚ_[p]) (hr : rho^2=2) (Pi M h : ℕ)
    (hpPi : p∣Pi) (hM : Entry p rho hr M) (hh : Nat.ModEq (Pi^3*M) h 0) (n : ℤ) :
    Near (ConcretePadic318.place p rho hr) 4 (chartU (n*(h:ℤ))) (chartV (n*(h:ℤ))) := by
  obtain ⟨k,hk⟩ := hpPi
  have hdiv : p^3*M∣Pi^3*M := ⟨k^3,by rw [hk]; ring⟩
  obtain ⟨m,hm⟩ := hdiv.trans (Nat.modEq_zero_iff_dvd.mp hh)
  have hindex : n*(h:ℤ)=(p:ℤ)^3*(M:ℤ)*(n*(m:ℤ)) := by
    rw [hm]
    push_cast
    ring
  rw [hindex]
  simpa only [show ((3:ℕ):ℤ)+1=4 by norm_num] using
    ValuativeOrbitMultiples318.prime_power_multiples (ConcretePadic318.place p rho hr)
      p (ActualSplitOrbitEntry318.prime_bound p rho hr) (M:ℤ)
      (ActualSplitOrbitEntry318.coefficient_bound p rho hr) (near p rho hr M hM) 3 (n*(m:ℤ))

/-- The opposite residue1 uses exactly M|(h−1), with no extra p-power and no
unjustified sign choice. The original duplication chart approaches(0,1). -/
theorem opposite (rho : ℚ_[p]) (hr : rho^2=2) (M h : ℕ)
    (hM : Entry p rho hr M) (hh : Nat.ModEq M h 1) (n : ℤ) :
    Near (ConcretePadic318.place p rho hr) 1
      (chartU (n*((h:ℤ)-1))) (chartV (n*((h:ℤ)-1))) := by
  have hd : (M:ℤ)∣(h:ℤ)-1 := by
    simpa only [Nat.cast_one] using Nat.modEq_iff_dvd.mp hh.symm
  obtain ⟨m,hm⟩ := hd
  have he := ValuativeOrbitMultiples318.near_int (ConcretePadic318.place p rho hr)
    1 (M:ℤ) (by norm_num) (ActualSplitOrbitEntry318.coefficient_bound p rho hr)
    (near p rho hr M hM) (n*m)
  have hindex : n*((h:ℤ)-1)=(n*m)*(M:ℤ) := by rw [hm]; ring
  simpa only [hindex] using he

end SelectedFormalEntry318
