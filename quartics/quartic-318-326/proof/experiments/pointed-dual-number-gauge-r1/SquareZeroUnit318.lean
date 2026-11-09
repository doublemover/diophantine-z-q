module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public section
noncomputable section
namespace SquareZeroUnit318
universe u v
variable (R : Type u) [CommRing R]
/-- The actual split square-zero extension, with its original multiplication. -/
abbrev Dual := TrivSqZeroExt R R
/-- The original infinitesimal unit, not a formal additive label. -/
@[expose] def unit (a : R) : (Dual R)ˣ where
  val := 1 + TrivSqZeroExt.inr a
  inv := 1 + TrivSqZeroExt.inr (-a)
  val_inv := by apply TrivSqZeroExt.ext <;> simp
  inv_val := by apply TrivSqZeroExt.ext <;> simp
@[simp] lemma unit_val (a : R) : (unit R a : Dual R) = 1 + TrivSqZeroExt.inr a := rfl
@[simp] lemma unit_zero : unit R 0 = 1 := by ext <;> simp [unit]
lemma unit_add (a b : R) : unit R (a + b) = unit R a * unit R b := by
  apply Units.ext
  apply TrivSqZeroExt.ext <;> simp [unit]
lemma unit_neg (a : R) : unit R (-a) = (unit R a)⁻¹ := by
  apply Units.ext
  rfl
lemma unit_injective : Function.Injective (unit R) := by
  intro a b h
  have := congrArg (fun z : (Dual R)ˣ => (z : Dual R).snd) h
  simpa [unit] using this
/-- Ring-functoriality changes BOTH the coefficient and square-zero coordinates. -/
@[expose] def map {S : Type v} [CommRing S] (f : R →+* S) : Dual R →+* Dual S where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by apply TrivSqZeroExt.ext <;> simp
  map_mul' x y := by apply TrivSqZeroExt.ext <;> simp [mul_comm]
@[simp] lemma map_fst {S : Type v} [CommRing S] (f : R →+* S) (z : Dual R) :
    (map R f z).fst = f z.fst := by simp [map]
@[simp] lemma map_snd {S : Type v} [CommRing S] (f : R →+* S) (z : Dual R) :
    (map R f z).snd = f z.snd := by simp [map]
lemma map_unit {S : Type v} [CommRing S] (f : R →+* S) (a : R) :
    Units.map (map R f).toMonoidHom (unit R a) = unit S (f a) := by
  apply Units.ext
  apply TrivSqZeroExt.ext <;> simp [map, unit]
/-- Every actual unit with reduction one has a unique square-zero coefficient. -/
lemma unit_eq_of_fst (z : (Dual R)ˣ) (h : (z : Dual R).fst = 1) :
    unit R (z : Dual R).snd = z := by
  apply Units.ext
  apply TrivSqZeroExt.ext <;> simp [unit, h]
lemma unit_iff (z : (Dual R)ˣ) :
    (z : Dual R).fst = 1 ↔ ∃! a : R, unit R a = z := by
  constructor
  · intro h
    refine ⟨(z : Dual R).snd, unit_eq_of_fst R z h, ?_⟩
    intro a ha
    apply unit_injective R
    exact ha.trans (unit_eq_of_fst R z h).symm
  · rintro ⟨a, rfl, _⟩
    simp [unit]
/-- The complete multiplicative cocycle law is the additive cocycle law. -/
lemma cocycle_iff (a b c : R) : unit R a * unit R b = unit R c ↔ a + b = c := by
  rw [← unit_add]
  exact (unit_injective R).eq_iff
/-- The actual gauge multiplication gives the additive coboundary, including sign. -/
lemma gauge (a b c : R) :
    unit R (-a) * unit R c * unit R b = unit R (c + b - a) := by
  rw [← unit_add, ← unit_add]
  congr 1
  ring
end SquareZeroUnit318
