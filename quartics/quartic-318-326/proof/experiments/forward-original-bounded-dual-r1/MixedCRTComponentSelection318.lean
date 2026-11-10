module
public import MonotheticComponentSteps318
public import PrimeCRTAssembly
public section

/-! The exact final mixed CRT progression, joined to component recurrence.
The fixed component return and nonempty target region remain explicit inputs. -/
namespace MixedCRTComponentSelection318
open Set TopologicalSpace
open MonotheticComponentSteps318
set_option maxHeartbeats 1000000

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [CompactSpace G]

/-- Every later point on the assembled progression retains each original
modulus. No relatively prime hypothesis is needed for this preservation step. -/
theorem progression_modEq (d r k t : ℕ) (hdk : d∣k) : Nat.ModEq d (r+k*t) r := by
  have hd : d∣k*t := dvd_mul_of_dvd_left hdk _
  simp [Nat.ModEq,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd]

/-- The three literal source residues and a nonempty real component region
are attained by the same arbitrarily large h. The target-region and component
return hypotheses are not replaced by full-product density. -/
theorem primary_depth_in_component_region
    (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (m : ℕ) (hm : m • a∈connectedComponent (0:G))
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16) (hh₀ : 16∣h₀)
    (hmdivL : m∣L) (hmdivh₀ : m∣h₀)
    (U : Set G) (ho : IsOpen U) (hne : ∃ x∈U, x∈connectedComponent (0:G)) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧ h • a∈U := by
  obtain ⟨r,hrA,hrP,hrL⟩ :=
    PrimeCRTAssembly.compatible_primary_depth Pi Mminus Mplus L h₀ e
      hPm hPL hmp hpL hmL hh₀
  let k : ℕ := Pi^e*Mminus*Mplus*L
  have hk : 0<k := by dsimp [k]; positivity
  have hmk : m∣k := dvd_mul_of_dvd_right hmdivL _
  have hmr : m∣r := Nat.modEq_zero_iff_dvd.mp
    ((hrL.of_dvd hmdivL).trans hmdivh₀.modEq_zero_nat)
  have hkcomp : k • a∈connectedComponent (0:G) := component_step_mem a m k hmk hm
  have hrcomp : r • a∈connectedComponent (0:G) := component_step_mem a m r hmr hm
  obtain ⟨t,ht,hU⟩ := component_positive_tail a hd k hk hkcomp (r • a) hrcomp U ho hne B
  have hkt : t≤k*t := by nlinarith
  have hpoint : r • a+t • (k • a)=(r+k*t) • a := by
    rw [add_nsmul,mul_smul,smul_comm k t]
  refine ⟨r+k*t,by omega,?_,?_,?_,?_⟩
  · apply (progression_modEq (Pi^e*Mminus) r k t ?_).trans hrA
    exact ⟨Mplus*L,by dsimp [k]; ring⟩
  · apply (progression_modEq Mplus r k t ?_).trans hrP
    exact ⟨Pi^e*Mminus*L,by dsimp [k]; ring⟩
  · apply (progression_modEq L r k t ?_).trans hrL
    exact ⟨Pi^e*Mminus*Mplus,by dsimp [k]; ring⟩
  · rwa [←hpoint]

/-- The source's factor 64 is retained explicitly. Even when m measures the
component of 2a, 64m returns a to the component. This is a subgroup statement,
not an unsupported identification of two different elliptic quotients. -/
theorem source64_return (a : G) (m : ℕ)
    (hm : m • (2 • a)∈connectedComponent (0:G)) :
    (64*m) • a∈connectedComponent (0:G) := by
  have he : (64*m) • a=32 • (m • (2 • a)) := by
    simp only [←mul_nsmul]
    congr 1
    ring
  rw [he]
  exact (AddSubgroup.connectedComponentOfZero G).nsmul_mem hm 32

/-- Exact 64m normalization for the final CRT source. The three residues are
kept distinct; neither h=0 nor h=1 modulo their product is substituted. -/
theorem primary_depth_source64
    (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (m : ℕ) (hm : m • (2 • a)∈connectedComponent (0:G))
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16)
    (hmdivL : 64*m∣L) (hmdivh₀ : 64*m∣h₀)
    (U : Set G) (ho : IsOpen U) (hne : ∃ x∈U, x∈connectedComponent (0:G)) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧ h • a∈U := by
  have h16 : 16∣h₀ := (show 16∣64*m from ⟨4*m,by ring⟩).trans hmdivh₀
  exact primary_depth_in_component_region a hd (64*m) (source64_return a m hm)
    Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL h16
    hmdivL hmdivh₀ U ho hne

end MixedCRTComponentSelection318
