module
public import ActualTwoDescentPrueferLevelCoordinates318
public import Mathlib.NumberTheory.Padics.RingHoms
public section
noncomputable section
namespace ActualTwoDescentPrueferEndResidues318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryGeometricCocycles318
open ActualTwoDescentCyclicEndCoordinates318 ActualTwoDescentAdditivePrimaryLevels318
open ActualTwoDescentPrueferLevelCoordinates318 ActualTwoDescentHigherCohomologyDirectedMaps318

local instance (k : ℕ) : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def prueferEndResidue (k : ℕ) : AddMonoid.End PrueferAdd →+* ZMod (2^k) :=
  (cyclicEndCoordinateHom (prueferLevelCoordinate k)).comp (additiveLevelEndHom PrueferAdd k)

lemma actual_pruefer_end_scalar (k : ℕ) (f : AddMonoid.End PrueferAdd)
    (x : PrueferAdd) (hx : (2^k) • x=0) : f x=(prueferEndResidue k f).val • x := by
  exact congrArg Subtype.val (actual_cyclic_end_scalar (prueferLevelCoordinate k)
    (additiveLevelEnd PrueferAdd k f) ⟨x,hx⟩)

/-- Finite-level endomorphism scalars are intrinsic, so arbitrary cyclic
coordinates still give the actual native reduction maps. -/
lemma actual_pruefer_end_residue_compatible (i j : ℕ) (h : i ≤ j) :
    (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^i))).comp (prueferEndResidue j)=prueferEndResidue i := by
  ext f
  let e := prueferLevelCoordinate i
  let x : PrueferLevel i := e 1
  have hx : (2^j) • x.val=0 := actual_nsmul_power_mono h x.property
  have he : additiveLevelEnd PrueferAdd i f x=(prueferEndResidue j f).val • x :=
    Subtype.ext (actual_pruefer_end_scalar j f x.val hx)
  have hc := congrArg e.symm he
  change prueferEndResidue i f=e.symm ((prueferEndResidue j f).val • e 1) at hc
  rw [map_nsmul,e.symm_apply_apply] at hc
  simpa only [RingHom.comp_apply,ZMod.castHom_apply,ZMod.cast_eq_val,nsmul_eq_mul,mul_one] using hc.symm

/-- The genuine actual endomorphism ring maps into native2-adic integers,
via their proved projective-limit universal property. -/
def prueferEndToPadic : AddMonoid.End PrueferAdd →+* ℤ_[2] :=
  PadicInt.lift actual_pruefer_end_residue_compatible

lemma actual_pruefer_end_to_padic_residue (k : ℕ) (f : AddMonoid.End PrueferAdd) :
    PadicInt.toZModPow k (prueferEndToPadic f)=prueferEndResidue k f :=
  congrArg (fun g => g f) (PadicInt.lift_spec actual_pruefer_end_residue_compatible k)

end ActualTwoDescentPrueferEndResidues318
