module
public import CharacterActualLocalDualNorm318
public section
noncomputable section
namespace DualUnitFactorization318
open SquareZeroUnit318
universe u v
variable (R : Type u) [CommRing R]
/-- The actual coefficient unit, under the original zero-section ring map. -/
@[expose] def coefficient : (Dual R)ˣ →* Rˣ :=
  Units.map (DualNumberScheme318.reductionRing R).toMonoidHom
@[expose] def lift : Rˣ →* (Dual R)ˣ :=
  Units.map (TrivSqZeroExt.inlHom R R).toMonoidHom
@[simp] lemma coefficient_lift (a : Rˣ) : coefficient R (lift R a) = a := by
  apply Units.ext
  rfl
@[simp] lemma coefficient_unit (a : R) : coefficient R (unit R a) = 1 := by
  apply Units.ext
  simp [coefficient, unit, DualNumberScheme318.reductionRing]
/-- Divide an arbitrary unit by its ACTUAL invertible coefficient. -/
@[expose] def normalized : (Dual R)ˣ →* (Dual R)ˣ where
  toFun z := (lift R (coefficient R z))⁻¹ * z
  map_one' := by simp
  map_mul' z w := by simp [mul_comm, mul_left_comm, mul_assoc]
lemma normalized_reduces (z : (Dual R)ˣ) : coefficient R (normalized R z) = 1 := by
  change coefficient R ((lift R (coefficient R z))⁻¹ * z) = 1
  rw [map_mul, map_inv, coefficient_lift, inv_mul_cancel]
@[expose] def log (z : (Dual R)ˣ) : R := (normalized R z).val.snd
lemma unit_log (z : (Dual R)ˣ) : unit R (log R z) = normalized R z :=
  unit_eq_of_fst R (normalized R z) (congrArg Units.val (normalized_reduces R z))
lemma factorization (z : (Dual R)ˣ) : lift R (coefficient R z) * unit R (log R z) = z := by
  rw [unit_log]
  change lift R (coefficient R z) * ((lift R (coefficient R z))⁻¹ * z) = z
  simp
@[simp] lemma log_unit (a : R) : log R (unit R a) = a := by
  apply unit_injective R
  rw [unit_log]
  change (lift R (coefficient R (unit R a)))⁻¹ * unit R a = unit R a
  rw [coefficient_unit, map_one, inv_one, one_mul]
@[simp] lemma log_lift (a : Rˣ) : log R (lift R a) = 0 := by
  apply unit_injective R
  rw [unit_log, unit_zero]
  change (lift R (coefficient R (lift R a)))⁻¹ * lift R a = 1
  rw [coefficient_lift, inv_mul_cancel]
@[simp] lemma log_one : log R 1 = 0 := by
  simpa only [map_one] using log_lift R 1
lemma log_mul (z w : (Dual R)ˣ) : log R (z * w) = log R z + log R w := by
  apply unit_injective R
  rw [unit_log, unit_add, unit_log, unit_log, map_mul]
variable {S : Type v} [CommRing S] (f : R →+* S)
lemma coefficient_natural (z : (Dual R)ˣ) :
    coefficient S (Units.map (map R f).toMonoidHom z) =
      Units.map f.toMonoidHom (coefficient R z) := by
  apply Units.ext
  exact map_fst R f z.val
lemma lift_natural (a : Rˣ) : Units.map (map R f).toMonoidHom (lift R a) =
    lift S (Units.map f.toMonoidHom a) := by
  apply Units.ext
  apply TrivSqZeroExt.ext <;> simp [lift, map]
lemma normalized_natural (z : (Dual R)ˣ) :
    normalized S (Units.map (map R f).toMonoidHom z) =
      Units.map (map R f).toMonoidHom (normalized R z) := by
  change (lift S (coefficient S (Units.map (map R f).toMonoidHom z)))⁻¹ * _ =
    Units.map (map R f).toMonoidHom ((lift R (coefficient R z))⁻¹ * z)
  rw [map_mul, map_inv, coefficient_natural, lift_natural]
lemma log_natural (z : (Dual R)ˣ) :
    log S (Units.map (map R f).toMonoidHom z) = f (log R z) := by
  dsimp only [log]
  rw [normalized_natural]
  exact map_snd R f (normalized R z).val
end DualUnitFactorization318
