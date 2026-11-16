module
public import PrueferBoundedCoordinates318
public import DyadicResidueInverseLimit318
public section
noncomputable section
namespace PrueferTateResidueBridge318
open ActualTwoDescentDyadicPrueferModel318 PrueferCanonicalTateTower318
open PrueferBoundedCoordinates318

/-- Reduction of a genuine residue has the expected bounded numerator. -/
theorem reduction_val (m n : ℕ) (h : m ≤ n) (a : ZMod (2^n)) :
    (DyadicResidueInverseLimit318.reduction m n h a).val = a.val % (2^m) := by
  rw [DyadicResidueInverseLimit318.reduction, ZMod.castHom_apply,
    ZMod.cast_eq_val, ZMod.val_natCast]

/-- Reconstruct the actual primary-component tower, level by level, using
its literal points 1/2^n in Q/Z. -/
def fromResidues : DyadicResidueInverseLimit318.residues →+
    PrimaryTateTower318.tower (Additive PrueferTwo) where
  toFun x := ⟨fun n => (x.val n).val • point n, by
    constructor
    · intro n
      rw [smul_comm, point_annihilated, nsmul_zero]
    · intro n
      have hc : (x.val (n+1)).val % (2^n) = (x.val n).val := by
        rw [← reduction_val n (n+1) (Nat.le_succ n)]
        exact congrArg ZMod.val (x.property n (n+1) (Nat.le_succ n))
      apply Subtype.ext
      change 2 • encode (n+1) (x.val (n+1)).val = encode n (x.val n).val
      rw [encode_transition, ← encode_mod n (x.val (n+1)).val, hc]⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    change ((0 : ZMod (2^n)).val) • point n = 0
    simp
  map_add' x y := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    change encode n (x.val n + y.val n).val =
      encode n (x.val n).val + encode n (y.val n).val
    rw [ZMod.val_add, encode_mod]
    exact add_nsmul _ _ _

/-- Every compatible actual tower supplies a compatible residue at every
level. All-level compatibility is proved from iterated doubling. -/
def toResidues (x : PrimaryTateTower318.tower (Additive PrueferTwo)) :
    DyadicResidueInverseLimit318.residues :=
  ⟨fun n => ((coordinate n (x.val n) (x.property.1 n)).val : ZMod (2^n)), by
    intro m n h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    apply ZMod.val_injective (2^m)
    rw [reduction_val, ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (coordinate (m+k) (x.val (m+k)) (x.property.1 (m+k))).isLt,
      Nat.mod_eq_of_lt (coordinate m (x.val m) (x.property.1 m)).isLt]
    exact tower_coordinate_reduction x m k⟩

theorem from_to (x : PrimaryTateTower318.tower (Additive PrueferTwo)) :
    fromResidues (toResidues x) = x := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change encode n
    (((coordinate n (x.val n) (x.property.1 n)).val : ZMod (2^n)).val) =
      (x.val n).toMul.val.toAdd
  rw [ZMod.val_natCast_of_lt (coordinate n (x.val n) (x.property.1 n)).isLt]
  exact coordinate_spec n (x.val n) (x.property.1 n)

theorem fromResidues_injective : Function.Injective fromResidues := by
  intro x y h
  apply Subtype.ext
  funext n
  apply ZMod.val_injective (2^n)
  apply encode_injective_bounded n _ _ (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun z : PrimaryTateTower318.tower (Additive PrueferTwo) =>
    (z.val n).toMul.val.toAdd) h

theorem to_from (x : DyadicResidueInverseLimit318.residues) :
    toResidues (fromResidues x) = x := by
  apply fromResidues_injective
  exact from_to (fromResidues x)

/-- An additive equivalence of the whole actual compatible tower, not a
pointwise choice of unrelated cyclic-group identifications. -/
def residueEquiv : DyadicResidueInverseLimit318.residues ≃+
    PrimaryTateTower318.tower (Additive PrueferTwo) where
  toFun := fromResidues
  invFun := toResidues
  left_inv := to_from
  right_inv := from_to
  map_add' := fromResidues.map_add

/-- The actual dyadic Prüfer Tate tower is additively Z2, via the compatible
residue construction and mathlib's p-adic inverse-limit theorem. -/
def padicEquiv : ℤ_[2] ≃+ PrimaryTateTower318.tower (Additive PrueferTwo) :=
  DyadicResidueInverseLimit318.padicEquiv.toAddEquiv.trans residueEquiv

/-- The distinguished unit maps to the previously constructed tower 1/2^n.
This fixes the normalization of the equivalence. -/
theorem padicEquiv_one : padicEquiv 1 = canonicalTower := by
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change encode n (PadicInt.toZModPow n 1).val = circle n
  rw [map_one, ← Nat.cast_one, ZMod.val_natCast, encode_mod]
  exact one_nsmul _

end PrueferTateResidueBridge318
