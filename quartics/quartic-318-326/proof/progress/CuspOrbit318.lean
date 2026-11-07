module
public import ReciprocalCuspCoordinate318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318
open scoped MatrixGroups
namespace CuspOrbit318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Equal genuine q-parameters differ by an integer translation. -/
theorem q_eq_translation (tau sigma:UpperHalfPlane)
    (h:Periodic.qParam 1 tau=Periodic.qParam 1 sigma) :
    ∃n:ℤ, tau=(n:ℝ)+ᵥsigma := by
  obtain ⟨m,hm⟩ := Periodic.qParam_left_inv_mod_period (by norm_num : (1:ℝ)≠0) (tau:ℂ)
  obtain ⟨n,hn⟩ := Periodic.qParam_left_inv_mod_period (by norm_num : (1:ℝ)≠0) (sigma:ℂ)
  rw [h] at hm
  have hh := hm.symm.trans hn
  refine ⟨n-m,?_⟩
  apply UpperHalfPlane.ext
  simp only [coe_vadd,Complex.ofReal_sub,Complex.ofReal_intCast]
  norm_num only [Complex.ofReal_one,mul_one] at hh
  push_cast
  linear_combination hh

/-- The actual standard infinity cusp has width one in Gamma1(N): every
integer translation, not only its Nth power, belongs to Gamma1(N). -/
theorem translation_mem (N:ℕ) (n:ℤ) : ModularGroup.T^n∈CongruenceSubgroup.Gamma1 N := by
  simp [CongruenceSubgroup.Gamma1_mem,ModularGroup.coe_T_zpow]

/-- Equal q-parameters represent the same genuine Gamma1 quotient point. -/
theorem quotient_eq_of_q_eq (N:ℕ) (tau sigma:UpperHalfPlane)
    (h:Periodic.qParam 1 tau=Periodic.qParam 1 sigma) :
    quotientMap N tau=quotientMap N sigma := by
  obtain ⟨n,hn⟩ := q_eq_translation tau sigma h
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  let gamma:CongruenceSubgroup.Gamma1 N := ⟨ModularGroup.T^n,translation_mem N n⟩
  let g:image N := ⟨positiveMatrix N gamma,⟨gamma,rfl⟩⟩
  refine ⟨g,?_⟩
  change ModularGroup.T^n • sigma=tau
  rw [modular_T_zpow_smul,hn]

/-- Actual reciprocal-j recovery gives a single high-region threshold,
without an assumed fundamental-domain or cusp-chart identification. -/
theorem exists_high_recovery : ∃A:ℝ, 0<A ∧ ∀tau:UpperHalfPlane, A<tau.im →
    ReciprocalCuspCoordinate318.inverseGerm ((ActualQJ318.jInvariant tau)⁻¹)=
      Periodic.qParam 1 tau := by
  obtain ⟨a,ha⟩ := atImInfty_mem _ |>.mp ReciprocalCuspCoordinate318.recover_q_eventually
  refine ⟨max a 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro tau htau
  exact ha tau (le_trans (le_max_left _ _) htau.le)

/-- On a sufficiently high actual cusp region, equality in the actual
Gamma1 quotient is exactly equality of q-parameters. -/
theorem exists_high_orbit_iff (N:ℕ) : ∃A:ℝ, 0<A ∧
    ∀tau sigma:UpperHalfPlane, A<tau.im → A<sigma.im →
      (quotientMap N tau=quotientMap N sigma ↔
        Periodic.qParam 1 tau=Periodic.qParam 1 sigma) := by
  obtain ⟨A,hA,hrec⟩ := exists_high_recovery
  refine ⟨A,hA,?_⟩
  intro tau sigma ht hs
  constructor
  · intro h
    have hj:ActualQJ318.jInvariant tau=ActualQJ318.jInvariant sigma := congrArg (jMap N) h
    rw [←hrec tau ht,←hrec sigma hs,hj]
  · exact quotient_eq_of_q_eq N tau sigma

end CuspOrbit318
