module
public import Mathlib.NumberTheory.Padics.RingHoms
public section
noncomputable section
namespace DyadicResidueInverseLimit318

/-- Reduction between the actual finite residue rings. -/
def reduction (m n : ℕ) (h : m ≤ n) : ZMod (2^n) →+* ZMod (2^m) :=
  ZMod.castHom (pow_dvd_pow 2 h) _

/-- The inverse limit is a subring of the dependent product, with every
reduction relation imposed. No cardinality or unchosen isomorphism replaces
these transition maps. -/
def residues : Subring (∀ n : ℕ, ZMod (2^n)) where
  carrier := {x | ∀ m n (h : m ≤ n), reduction m n h (x n) = x m}
  zero_mem' := by intros; exact map_zero _
  one_mem' := by intros; exact map_one _
  add_mem' := by
    intro x y hx hy m n h
    change reduction m n h (x n + y n) = x m + y m
    rw [map_add, hx m n h, hy m n h]
  mul_mem' := by
    intro x y hx hy m n h
    change reduction m n h (x n * y n) = x m * y m
    rw [map_mul, hx m n h, hy m n h]
  neg_mem' := by
    intro x hx m n h
    change reduction m n h (-x n) = -x m
    rw [map_neg, hx m n h]

/-- A coordinate projection is a ring hom, as required by PadicInt.lift. -/
def coordinate (n : ℕ) : residues →+* ZMod (2^n) where
  toFun x := x.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

 theorem coordinate_compatible (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow 2 h) _).comp (coordinate n) = coordinate m := by
  ext x
  exact x.property m n h

/-- The canonical map from 2-adic integers to their compatible residues. -/
def toResidues : ℤ_[2] →+* residues where
  toFun z := ⟨fun n => PadicInt.toZModPow n z, by
    intro m n h
    exact congrArg (fun f : ℤ_[2] →+* ZMod (2^m) => f z)
      (PadicInt.zmod_cast_comp_toZModPow m n h)⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ x y
  map_mul' x y := by apply Subtype.ext; funext n; exact map_mul _ x y

/-- Existence of the 2-adic integer uses mathlib's actual inverse-limit
construction, applied to the compatible coordinate ring homomorphisms. -/
def fromResidues : residues →+* ℤ_[2] :=
  PadicInt.lift coordinate_compatible

 theorem fromResidues_coordinate (x : residues) (n : ℕ) :
    PadicInt.toZModPow n (fromResidues x) = x.val n := by
  exact congrArg (fun f : residues →+* ZMod (2^n) => f x)
    (PadicInt.lift_spec coordinate_compatible n)

 theorem from_to (z : ℤ_[2]) : fromResidues (toResidues z) = z := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact fromResidues_coordinate (toResidues z) n

 theorem to_from (x : residues) : toResidues (fromResidues x) = x := by
  apply Subtype.ext
  funext n
  exact fromResidues_coordinate x n

/-- A ring equivalence with the literal compatible dyadic residue system.
This alone makes no assertion identifying a Selmer or Prüfer Tate tower. -/
def padicEquiv : ℤ_[2] ≃+* residues where
  toFun := toResidues
  invFun := fromResidues
  left_inv := from_to
  right_inv := to_from
  map_add' := toResidues.map_add
  map_mul' := toResidues.map_mul

end DyadicResidueInverseLimit318
