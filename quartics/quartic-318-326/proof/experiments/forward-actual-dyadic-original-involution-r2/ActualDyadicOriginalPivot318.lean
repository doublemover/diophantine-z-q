module
public import ActualDyadicCongruenceSwitch318
public section
noncomputable section
namespace ActualDyadicOriginalPivot318
open QuadricCRTAssembly318 ActualOriginalCoordinateBump318 ActualOddRegularLift318
open ActualOriginalModularLift318
set_option maxHeartbeats 28000000

lemma actual_regular_coordinate {R : Type*} [Zero R] (x : Coordinates R) (hx : Regular x) :
    ∃i : Fin 4,coordinate x i≠0 := by
  by_contra hh
  push_neg at hh
  exact hx (Prod.ext (Prod.ext (hh 0) (hh 1)) (Prod.ext (hh 2) (hh 3)))

/-- The pivot depends ONLY on the original residue modulo2. -/
@[expose] def pivot (x : Coordinates (ZMod 2)) : Fin 4 := by
  classical
  exact if h : Regular x then Classical.choose (actual_regular_coordinate x h) else 0
lemma pivot_one (x : Coordinates (ZMod 2)) (hx : Regular x) : coordinate x (pivot x)=1 := by
  classical
  have hh : coordinate x (pivot x)≠0 := by
    simpa only [pivot,dif_pos hx] using Classical.choose_spec (actual_regular_coordinate x hx)
  generalize he : coordinate x (pivot x)=z at hh ⊢
  fin_cases z <;> norm_num at hh ⊢

@[expose] def modulus (e : ℕ) : ℕ := 2^(e+3)
@[expose] def half (e : ℕ) : ℕ := 2^(e+2)
instance modulusNeZero (e : ℕ) : NeZero (modulus e) := ⟨pow_ne_zero _ (by norm_num)⟩
lemma two_dvd_modulus (e : ℕ) : 2∣modulus e := dvd_pow_self _ (by omega)
lemma two_dvd_half (e : ℕ) : 2∣half e := dvd_pow_self _ (by omega)
@[expose] def reduction (e : ℕ) : ZMod (modulus e) →+* ZMod 2 :=
  ZMod.castHom (two_dvd_modulus e) (ZMod 2)
@[expose] def low (e : ℕ) (x : Coordinates (ZMod (modulus e))) : Coordinates (ZMod 2) :=
  mapCoordinates (reduction e) x
@[expose] def step (e : ℕ) : ZMod (modulus e) := (half e:ℕ)

lemma low_integer_digits (e : ℕ) (x : Coordinates (ZMod (modulus e))) :
    low e x=mapCoordinates (Int.castRingHom (ZMod 2)) (digits (modulus e) x) := by
  have hs (z : ZMod (modulus e)) : reduction e z=(z.val:ZMod 2) := by
    have hh := congrArg (reduction e) (ZMod.natCast_zmod_val z)
    simpa only [map_natCast] using hh.symm
  simp only [low,mapCoordinates,digits,Int.castRingHom_apply,Int.cast_natCast]
  exact Prod.ext (Prod.ext (hs x.1.1) (hs x.1.2))
    (Prod.ext (Prod.ext (hs x.2.1.1) (hs x.2.1.2)) (hs x.2.2))

lemma step_reduces_zero (e : ℕ) : reduction e (step e)=0 := by
  change reduction e (half e:ℕ)=0
  rw [map_natCast]
  have hh : ((half e:ℤ):ZMod 2)=0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (by exact_mod_cast two_dvd_half e)
  simpa only [Int.cast_natCast] using hh
lemma step_twice_zero (e : ℕ) : step e+step e=0 := by
  have hn : half e+half e=modulus e := by
    unfold half modulus
    rw [show e+3=(e+2)+1 by omega,pow_succ 2 (e+2)]
    omega
  have hh := congrArg (fun n : ℕ => (n:ZMod (modulus e))) hn
  simpa only [Nat.cast_add,ZMod.natCast_self,step] using hh

@[expose] def toggle (e : ℕ) (x : Coordinates (ZMod (modulus e))) : Coordinates (ZMod (modulus e)) :=
  bump (pivot (low e x)) (step e) x
lemma toggle_low (e : ℕ) (x : Coordinates (ZMod (modulus e))) : low e (toggle e x)=low e x := by
  unfold low toggle
  rw [bump_map,step_reduces_zero,bump_zero]
lemma toggle_involutive (e : ℕ) : Function.Involutive (toggle e) := by
  intro x
  change bump (pivot (low e (toggle e x))) (step e)
    (bump (pivot (low e x)) (step e) x)=x
  rw [toggle_low,bump_add,step_twice_zero,bump_zero]

/-- The actual residue toggle is exactly the reduction of the literal
integer coordinate bump used in the next-congruence calculation. -/
lemma actual_toggle_integer_formula (e : ℕ) (x : Coordinates (ZMod (modulus e))) :
    toggle e x=mapCoordinates (Int.castRingHom (ZMod (modulus e)))
      (bump (pivot (low e x)) (half e:ℤ) (digits (modulus e) x)) := by
  rw [bump_map,digits_reduce]
  simp only [toggle,step,Int.castRingHom_apply,Int.cast_natCast]

lemma actual_pivot_integer_odd (e : ℕ) (x : Coordinates (ZMod (modulus e))) (hx : Regular (low e x)) :
    (coordinate (digits (modulus e) x) (pivot (low e x)):ZMod 2)=1 := by
  calc
    _ = coordinate (mapCoordinates (Int.castRingHom (ZMod 2)) (digits (modulus e) x))
        (pivot (low e x)) := (coordinate_map _ _ _).symm
    _ = coordinate (low e x) (pivot (low e x)) :=
      congrArg (fun z => coordinate z (pivot (low e x))) (low_integer_digits e x).symm
    _ = 1 := pivot_one (low e x) hx

end ActualDyadicOriginalPivot318
