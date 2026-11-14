module
public import ActualDyadicQuadricInvolution318
public section
noncomputable section
namespace ActualDyadicRegularRecurrence318
open QuadricCRTAssembly318 ActualOddRegularResidueTower318 ActualPrimitiveResidueLiftSet318
open ActualDyadicOriginalPivot318 ActualDyadicQuadricInvolution318 ActualDyadicAmbientLift318
open ActualAmbientQuadricLift318
open scoped BigOperators
set_option maxHeartbeats 30000000

@[expose] def originalRegularEquiv (κ : ℤ) (e : ℕ) :
    RegularResidues κ (modulus e) 2 ≃ Space κ e where
  toFun x := ⟨x.1,by
    rw [low_integer_digits]
    exact x.2⟩
  invFun x := ⟨x.1,by
    change ActualOddRegularLift318.Regular (mapCoordinates (Int.castRingHom (ZMod 2))
      (ActualOriginalModularLift318.digits (modulus e) x.1.1))
    rw [←low_integer_digits]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def originalSetEquiv (κ : ℤ) (e : ℕ) :
    ↥(regularSet κ (modulus e) 2) ≃ Space κ e where
  toFun x := (originalRegularEquiv κ e) ⟨x.1,(mem_regularSet κ (modulus e) 2 x.1).mp x.2⟩
  invFun x := ⟨x.1,(mem_regularSet κ (modulus e) 2 x.1).mpr ((originalRegularEquiv κ e).symm x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def originalSigmaEquiv (κ : ℤ) (e : ℕ) :
    (Σx : ↥(regularSet κ (modulus e) 2),QuadricFiber κ (modulus e) 2 x.1) ≃
      (Σx : Space κ e,QuadricFiber κ (modulus e) 2 x.1) where
  toFun z := ⟨originalSetEquiv κ e z.1,z.2⟩
  invFun z := ⟨(originalSetEquiv κ e).symm z.1,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All actual regular next-level residues are partitioned by their
actual original base class, not by independently chosen digit tuples. -/
@[expose] def originalNextEquiv (κ : ℤ) (e : ℕ) :
    RegularResidues κ (modulus e*2) 2 ≃
      (Σx : Space κ e,QuadricFiber κ (modulus e) 2 x.1) :=
  (regularPreimageEquiv κ (modulus e) 2 (two_dvd_modulus e)).trans
    ((preimageEquiv κ (modulus e) 2 (regularSet κ (modulus e) 2)).trans
      (originalSigmaEquiv κ e))

/-- The actual32-or0 fibers and the constructed congruence-switching
involution combine to give16 times the original regular base count.
This is an average over paired base classes, NEVER16 per base class. -/
theorem actual_dyadic_regular_step (κ : ℤ) (e : ℕ) :
    Nat.card (RegularResidues κ (modulus e*2) 2)=
      Nat.card (RegularResidues κ (modulus e) 2)*16 := by
  classical
  letI : ∀x : Space κ e,Fintype (QuadricFiber κ (modulus e) 2 x.1) :=
    fun _ => Fintype.ofFinite _
  have hcount : Nat.card (RegularResidues κ (modulus e*2) 2)=
      Nat.card {x : Space κ e // Successful κ e x}*32 := by
    rw [Nat.card_congr (originalNextEquiv κ e),Nat.card_eq_fintype_card,Fintype.card_sigma]
    calc
      _ = ∑x : Space κ e,if Successful κ e x then 32 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        simpa only [Nat.card_eq_fintype_card] using
          actual_dyadic_ambient_count κ (modulus e) (two_dvd_modulus e) x.1
      _ = _ := by
        rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
  rw [hcount,Nat.card_congr (originalRegularEquiv κ e),actual_successful_half]
  ring

/-- Every genuine original dyadic level n>=3 has the regular count
recurrence. kappa can be arbitrary here; its valuation is used only
later to identify this regular locus with the primitive source. -/
theorem actual_dyadic_regular_prime_power_step (κ : ℤ) (e : ℕ) :
    Nat.card (RegularResidues κ (2^(e+4)) 2)=Nat.card (RegularResidues κ (2^(e+3)) 2)*16 := by
  have he : 2^(e+4)=modulus e*2 := by
    unfold modulus
    rw [show e+4=(e+3)+1 by omega,pow_succ]
  rw [he]
  exact actual_dyadic_regular_step κ e

end ActualDyadicRegularRecurrence318
