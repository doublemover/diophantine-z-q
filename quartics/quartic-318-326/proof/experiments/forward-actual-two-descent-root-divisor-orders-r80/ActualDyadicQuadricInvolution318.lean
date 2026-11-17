module
public import ActualDyadicOriginalPivot318
public section
noncomputable section
namespace ActualDyadicQuadricInvolution318
open QuadricCRTAssembly318 ActualOriginalCoordinateBump318 ActualOddRegularLift318
open ActualOriginalModularLift318 ActualDyadicOriginalPivot318 ActualDyadicCongruenceSwitch318
open ActualIntegerRepresentativeCongruence318 ActualDyadicAmbientLift318
set_option maxHeartbeats 30000000

@[expose] def Space (κ : ℤ) (e : ℕ) :=
  {x : Quadric (κ:ZMod (modulus e)) // Regular (low e x.1)}
@[expose] def Successful (κ : ℤ) (e : ℕ) (x : Space κ e) : Prop :=
  Next κ (modulus e:ℤ) (digits (modulus e) x.1.1)

lemma actual_toggle_quadric (κ : ℤ) (e : ℕ) (x : Space κ e) :
    equation (κ:ZMod (modulus e)) (toggle e x.1.1)=0 := by
  let X := digits (modulus e) x.1.1
  let i := pivot (low e x.1.1)
  have hi : (coordinate X i:ZMod 2)=1 := actual_pivot_integer_odd e x.1.1 x.2
  have hQ : (modulus e:ℤ)∣equation κ X :=
    ActualAmbientQuadricLift318.actual_base_divides κ (modulus e) x.1
  have hb : 2*(modulus e:ℤ)∣equation κ (bump i (half e:ℤ) X)-equation κ X-(modulus e:ℤ) := by
    simpa only [modulus,half,Nat.cast_pow,Nat.cast_ofNat] using
      actual_odd_coordinate_toggle κ e i X hi
  have hd : (modulus e:ℤ)∣equation κ (bump i (half e:ℤ) X)-equation κ X-(modulus e:ℤ) :=
    (dvd_mul_left (modulus e:ℤ) 2).trans hb
  have hy : (modulus e:ℤ)∣equation κ (bump i (half e:ℤ) X) := by
    have hh := dvd_add (dvd_add hd hQ) (dvd_refl (modulus e:ℤ))
    convert hh using 1 <;> ring
  rw [actual_toggle_integer_formula,equation_map]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ (modulus e)).mpr hy

@[expose] def actualToggle (κ : ℤ) (e : ℕ) (x : Space κ e) : Space κ e :=
  ⟨⟨toggle e x.1.1,actual_toggle_quadric κ e x⟩,by
    change Regular (low e (toggle e x.1.1))
    rw [toggle_low]
    exact x.2⟩
lemma actualToggle_involutive (κ : ℤ) (e : ℕ) : Function.Involutive (actualToggle κ e) := by
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact toggle_involutive e x.1.1

/-- The actual canonical next-level test really is reversed by this
ORIGINAL residue involution, including all carries and sign conventions. -/
theorem actualToggle_switches (κ : ℤ) (e : ℕ) (x : Space κ e) :
    Successful κ e (actualToggle κ e x) ↔ ¬Successful κ e x := by
  let X := digits (modulus e) x.1.1
  let i := pivot (low e x.1.1)
  have hi : (coordinate X i:ZMod 2)=1 := actual_pivot_integer_odd e x.1.1 x.2
  have hQ : (2:ℤ)^(e+3)∣equation κ X := by
    simpa only [modulus,Nat.cast_pow,Nat.cast_ofNat] using
      ActualAmbientQuadricLift318.actual_base_divides κ (modulus e) x.1
  have hs : (2*(modulus e:ℤ)∣equation κ (bump i (half e:ℤ) X)) ↔
      ¬(2*(modulus e:ℤ)∣equation κ X) := by
    simpa only [modulus,half,Nat.cast_pow,Nat.cast_ofNat] using
      actual_integer_toggle_switch κ e i X hQ hi
  change (2*(modulus e:ℤ)∣equation κ (digits (modulus e) (toggle e x.1.1))) ↔
    ¬(2*(modulus e:ℤ)∣equation κ X)
  rw [actual_toggle_integer_formula,
    actual_canonical_next_test κ (modulus e) (two_dvd_modulus e)]
  exact hs

/-- Half of the original regular base classes, and EXACTLY half,
have all32 next-level lifts. The half is now CONSTRUCTED. -/
theorem actual_successful_half (κ : ℤ) (e : ℕ) :
    Nat.card (Space κ e)=Nat.card {x : Space κ e // Successful κ e x}*2 := by
  classical
  exact FiniteCongruenceSwitchPairing318.actual_half_card _ _
    (actualToggle_involutive κ e) (actualToggle_switches κ e)

end ActualDyadicQuadricInvolution318
