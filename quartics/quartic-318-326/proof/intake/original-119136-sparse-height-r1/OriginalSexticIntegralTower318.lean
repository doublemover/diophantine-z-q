module
public import OriginalSeparableSexticJet318

/-! Integer coordinate model for a biquadratic tower plus one relative
square root. All data are interpreted in the one field of the receiver.
The multiplication lemmas are universal identities, so checking a numerical
certificate in the copyable small coordinate algebra is not an extra oracle. -/
public section
noncomputable section

namespace OriginalSexticIntegralTower318

open Polynomial

abbrev V4 := ℤ × ℤ × ℤ × ℤ
abbrev V8 := V4 × V4

@[expose] def m4 (A B : ℤ) (u v : V4) : V4 :=
  let a := u.1; let b := u.2.1; let c := u.2.2.1; let d := u.2.2.2
  let e := v.1; let f := v.2.1; let g := v.2.2.1; let h := v.2.2.2
  (a*e + A*b*f + B*c*g + A*B*d*h,
   a*f + b*e + B*c*h + B*d*g,
   a*g + c*e + A*b*h + A*d*f,
   a*h + b*g + c*f + d*e)

@[expose] def m8 (A B : ℤ) (R : V4) (u v : V8) : V8 :=
  (m4 A B u.1 v.1 + m4 A B R (m4 A B u.2 v.2),
   m4 A B u.1 v.2 + m4 A B u.2 v.1)

@[expose] def unit : V8 := ((1,0,0,0),0)

variable {E : Type*} [CommRing E]

@[expose] def read4 (a b : E) (u : V4) : E :=
  u.1 + (u.2.1 : E)*a + (u.2.2.1 : E)*b + (u.2.2.2 : E)*(a*b)

@[simp] theorem read4_zero (a b : E) : read4 a b 0 = 0 := by simp [read4]

@[simp] theorem read4_add (a b : E) (u v : V4) :
    read4 a b (u + v) = read4 a b u + read4 a b v := by
  simp only [read4, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem read4_mul (a b : E) (A B : ℤ) (ha : a^2 = A) (hb : b^2 = B)
    (u v : V4) : read4 a b (m4 A B u v) = read4 a b u * read4 a b v := by
  simp only [m4, read4, Int.cast_add, Int.cast_mul]
  rw [← ha, ← hb]
  ring

@[expose] def read8 (a b r : E) : V8 →+ E where
  toFun v := read4 a b v.1 + read4 a b v.2 * r
  map_zero' := by simp
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, read4_add]
    ring

@[simp] theorem read8_unit (a b r : E) : read8 a b r unit = 1 := by
  simp [read8, read4, unit]

theorem read8_mul (a b r : E) (A B : ℤ) (R : V4)
    (ha : a^2 = A) (hb : b^2 = B) (hr : r^2 = read4 a b R) (u v : V8) :
    read8 a b r (m8 A B R u v) = read8 a b r u * read8 a b r v := by
  change read4 a b (m4 A B u.1 v.1 + m4 A B R (m4 A B u.2 v.2)) +
    read4 a b (m4 A B u.1 v.2 + m4 A B u.2 v.1) * r = _
  simp only [read8, AddMonoidHom.coe_mk, ZeroHom.coe_mk, read4_add, read4_mul a b A B ha hb]
  rw [← hr]
  ring

end OriginalSexticIntegralTower318

#print axioms OriginalSexticIntegralTower318.read8_mul
