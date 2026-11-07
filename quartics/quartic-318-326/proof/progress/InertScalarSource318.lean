module
public import InertLogHom318
public import ScalarPlaceBridge318
public import TorsionSafeIndex318
public section
namespace InertScalarSource318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay
open scoped QuadraticAlgebra
open CompressedOrientation318 CompressedPoint318 ScalarSource318
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime] (ns:¬∃x:ZMod p,x^2=2)
local notation "L" => InertCompletion318.Field p ns
local notation "φ" => InertCompletion318.embedding p ns
local notation "v" => InertPlace318.place p ns

theorem not_dvd_small (n:ℕ) (hn:0<n) (hsmall:n<p) : ¬p∣n :=
  fun hd=>not_le_of_gt hsmall (Nat.le_of_dvd hn hd)

theorem prime_norm_power (k:ℕ) : ‖(p:ℚ_[p])‖^k=(p:ℝ)^(-(k:ℤ)) := by
  simp [Padic.norm_p,zpow_neg]

/-- Literal scalar source yields actual completed-field formality and the
full relative norm gain, with no local analytic or group premise. -/
theorem source_norm_bounds (hp:19≤p)
    (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (rval:ℤ) (hr:ConcretePadic318.rationalPlace p (r w)=rval) (hpos:0<rval) (hodd:Odd rval) :
    φ (fH w)≠0 ∧ φ (fR w)≠0 ∧
    ‖φ (fH w)‖≤‖(p:ℚ_[p])‖^2 ∧ ‖φ (fR w)‖≤‖(p:ℚ_[p])‖^2 ∧
    ‖φ (fR w)‖≤‖(p:ℚ_[p])‖^16*‖φ (fH w)‖ := by
  have hp2:=not_dvd_small p 2 (by decide) (by omega)
  have hp3:=not_dvd_small p 3 (by decide) (by omega)
  have hp7:=not_dvd_small p 7 (by decide) (by omega)
  have hp11:=not_dvd_small p 11 (by decide) (by omega)
  have hp17:=not_dvd_small p 17 (by decide) (by omega)
  obtain ⟨hHpos,hrel⟩:=ScalarPlaceBridge318.inert_source p ns S w source rval hr hpos hodd
    hp2 hp3 hp7 hp11 hp17
  have hD:v CompressedOrientation318.D=0 :=
    (SourcePadic318.discriminant_units v (InertPlace318.place_two p ns)
      (InertSourceExclusion318.place_nat_unit p ns 3 hp3)
      (InertSourceExclusion318.place_nat_unit p ns 7 hp7)).2
  obtain ⟨a,ha,haeven⟩:=ScalarLocalValues318.source_fH_even S w source v hD
  obtain ⟨b,hb,hbeven⟩:=ScalarLocalValues318.source_fR_even S w source v
  have ha2:2≤a := by
    rw [ha] at hHpos
    have hapos:0<a := by exact_mod_cast hHpos
    obtain ⟨j,hj⟩:=haeven
    omega
  have hba:16≤b-a := by
    rw [(InertPlace318.place p ns).map_div,hb,ha] at hrel
    rw [←WithTop.LinearOrderedAddCommGroup.coe_sub] at hrel
    exact WithTop.coe_le_coe.mp hrel
  have hb2:2≤b := by omega
  have hH0:fH w≠0:=source_fH_ne S w source
  have hR0:fR w≠0:=((InertPlace318.place p ns).ne_top_iff).mp (by rw [hb]; simp)
  have hHφ:φ (fH w)≠0:=fun he=>hH0 ((InertCompletion318.embedding p ns).injective (by simpa using he))
  have hRφ:φ (fR w)≠0:=fun he=>hR0 ((InertCompletion318.embedding p ns).injective (by simpa using he))
  refine ⟨hHφ,hRφ,?_,?_,?_⟩
  · rw [prime_norm_power]
    apply (InertCompletion318.norm_bound_iff p ns (fH w) 2).mpr
    rw [ha]; exact_mod_cast ha2
  · rw [prime_norm_power]
    apply (InertCompletion318.norm_bound_iff p ns (fR w) 2).mpr
    rw [hb]; exact_mod_cast hb2
  · have hn:‖φ (fR w/fH w)‖≤‖(p:ℚ_[p])‖^16 := by
      rw [prime_norm_power]
      exact (InertCompletion318.norm_bound_iff p ns _ 16).mpr hrel
    rw [map_div₀,norm_div] at hn
    exact (div_le_iff₀ (norm_pos_iff.mpr hHφ)).mp hn

end InertScalarSource318
#print axioms InertScalarSource318.source_norm_bounds
