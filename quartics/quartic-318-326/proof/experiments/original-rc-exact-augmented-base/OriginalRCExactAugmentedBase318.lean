module
public import OriginalRCActualTerminalCertificate318
import Mathlib.Tactic.Ring

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCExactAugmentedBase318
open OriginalRCTerminalWindow318 OriginalRCLiteralTerminalRows318
open OriginalRCActualTerminalCertificate318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {R G : Type*} [CommRing R] [Group G]
variable {b M : ℕ}

/-- Trivial sign is augmentation in the original group algebra; this
does not evaluate t=0 on the Laurent coefficient ring. -/
@[expose] def augment : MonoidAlgebra R G →+* R :=
  MonoidAlgebra.liftNCRingHom (RingHom.id R) (1 : G →* R)
    (fun r g => mul_comm _ _)

theorem reduce_augmented_base (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi₀ : G →* Series M) (f : MonoidAlgebra R G)
    (hchi : ∀ S : Finset (Fin b), chi₀ (label S) = 1) :
    evaluate rho chi₀ f = rho (augment f) := by
  classical
  let term : Finset (Fin b) → MonoidAlgebra R G :=
    fun S => MonoidAlgebra.single (label S) (f.coeff (label S))
  have he : (∑ S, term S) = f := basis_expansion label f
  calc
    _ = evaluate rho chi₀ (∑ S, term S) := congrArg (evaluate rho chi₀) he.symm
    _ = rho (augment (∑ S, term S)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      simp [term, evaluate, augment, hchi]
    _ = _ := congrArg (fun T => rho (augment T)) he

/-- Exact coefficient descent: one characteristic-zero row identity and
its genuine integral scaled factor give the full integral scaled product.
No finite residue is used at this step. -/
theorem scaled_exact_product {A K : Type*} [CommRing A] [CommRing K]
    (ι : A →+* K) (hi : Function.Injective ι)
    (f d U : PowerSeries A) (V : PowerSeries K) (s : A)
    (hd : PowerSeries.map ι d = PowerSeries.map ι f * V)
    (hU : PowerSeries.map ι U = PowerSeries.C (ι s) * V) :
    PowerSeries.C s * d = f * U := by
  apply PowerSeries.map_injective ι hi
  rw [map_mul, map_mul, PowerSeries.map_C, hd, hU]
  ring

/-- Literal reduction of the same integral product used to prove the
exact characteristic-zero center. -/
theorem reduce_scaled_product (c : ℕ) (f d U : PowerSeries ℤ_[2])
    (hprod : PowerSeries.C ((2 : ℤ_[2])^c) * d = f * U) :
    HahnSeries.C ((2 : Residue M)^c) * finiteRegular M d =
      finiteRegular M f * finiteRegular M U := by
  have h := congrArg (finiteRegular M) hprod
  simpa only [finiteRegular_eq, map_mul, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
    map_pow, map_ofNat] using h

theorem regular_constant_residue (F : PowerSeries ℤ_[2]) :
    (finiteRegular M F).coeff 0 = PadicInt.toZModPow M (PowerSeries.constantCoeff F) := by
  rw [finiteRegular_eq]
  simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    normal_constant_map] using
    (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (PowerSeries.map (PadicInt.toZModPow M) F) 0)

/-- The exact constant of the original scaled regular series is zero
when the genuine numerator constant is zero and f₀(0)≠0. -/
theorem scaled_constant_zero {A : Type*} [CommRing A] [IsDomain A]
    (f d U : PowerSeries A) (s : A)
    (hprod : PowerSeries.C s * d = f * U)
    (hf : PowerSeries.constantCoeff f ≠ 0) (hd : PowerSeries.constantCoeff d = 0) :
    PowerSeries.constantCoeff U = 0 := by
  have h := congrArg (fun P : PowerSeries A => PowerSeries.constantCoeff P) hprod
  have hz : PowerSeries.constantCoeff f * PowerSeries.constantCoeff U = 0 := by
    simpa only [map_mul, PowerSeries.constantCoeff_C, hd, mul_zero] using h.symm
  exact (mul_eq_zero.mp hz).resolve_left hf

end OriginalRCExactAugmentedBase318

#print axioms OriginalRCExactAugmentedBase318.scaled_exact_product
