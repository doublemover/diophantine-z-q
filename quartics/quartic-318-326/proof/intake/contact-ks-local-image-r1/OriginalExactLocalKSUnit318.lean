module
public import SectionHeight318
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

public section
noncomputable section
namespace OriginalExactLocalKSUnit318

open NumberField SectionHeight318
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {E : Type u} [Field E] [NumberField E]
variable (w : FinitePlace E)
local notation "O" => 𝓞 E
@[expose] abbrev placePrime (v : FinitePlace E) : Ideal (𝓞 E) :=
  (FinitePlace.maximalIdeal v).asIdeal

/-- The actual arithmetic local ring at w, embedded in the single
common height field. This is the canonical localization as a
subalgebra of E, not a completed or newly chosen valuation field. -/
@[expose] def localRing : Subalgebra O E :=
  Localization.subalgebra E (placePrime w).primeCompl (placePrime w).primeCompl_le_nonZeroDivisors

local notation "V" => localRing w

theorem unit_norm (u : Vˣ) : w (↑(u:V):E) = 1 := by
  letI : IsLocalization (placePrime w).primeCompl V :=
    Localization.subalgebra.isLocalization_subalgebra E (placePrime w).primeCompl (placePrime w).primeCompl_le_nonZeroDivisors
  obtain ⟨⟨x,y⟩, e⟩ := IsLocalization.surj (placePrime w).primeCompl (u:V)
  have s : IsUnit (algebraMap O V x) :=
    e ▸ u.isUnit.mul (IsLocalization.map_units V y)
  have hx : x ∉ placePrime w := (IsLocalization.AtPrime.isUnit_to_map_iff V (placePrime w) x).mp s
  have nx : w (algebraMap O E x) = 1 :=
    (FinitePlace.norm_embedding_eq w _).symm.trans
      ((FinitePlace.norm_eq_one_iff_notMem E (FinitePlace.maximalIdeal w) x).mpr hx)
  have ny : w (algebraMap O E (y:O)) = 1 :=
    (FinitePlace.norm_embedding_eq w _).symm.trans
      ((FinitePlace.norm_eq_one_iff_notMem E (FinitePlace.maximalIdeal w) (y:O)).mpr y.2)
  have eg := congrArg (fun z : V => w (z:E)) e
  change w ((↑(u:V):E)*(algebraMap O E (y:O))) = w (algebraMap O E x) at eg
  rw [map_mul w,nx,ny,mul_one] at eg
  exact eg

/-- A genuine equality of rank-one arithmetic lattices yields the
actual primitive frame multiplier in the local ring. The two
coordinate coefficients are allowed to be fractional. -/
theorem primitive_unit (a b : E) (hb : b ≠ 0)
    (equal : Submodule.span V ({a} : Set E) = Submodule.span V ({b} : Set E)) :
    ∃ u : Vˣ, a = (↑(u:V):E)*b := by
  have ba : b ∈ Submodule.span V ({a} : Set E) :=
    equal.symm ▸ Submodule.mem_span_singleton_self b
  have ab : a ∈ Submodule.span V ({b} : Set E) :=
    equal ▸ Submodule.mem_span_singleton_self a
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp ab
  obtain ⟨s,hs⟩ := Submodule.mem_span_singleton.mp ba
  change ((r:V):E)*b = a at hr
  change ((s:V):E)*a = b at hs
  have e : ((r*s:V):E) = 1 := by
    apply mul_right_cancel₀ hb
    calc
      _ = (s:E)*((r:E)*b) := by change ((r:E)*(s:E))*b = _; ac_rfl
      _ = b := by rw [hr,hs]
      _ = 1*b := (one_mul _).symm
  have ei : r*s = 1 := Subtype.val_injective e
  obtain ⟨u,hu⟩ := IsUnit.of_mul_eq_one s ei
  exact ⟨u,hr.symm.trans (by rw [hu])⟩

/-- The exact finite input for InducedLattice applied to the
transported frame Q*=kQ. Integral equality is the genuine local
image equality Ψ(H²)=210C, expressed in the one Q-coefficient field.
This proof does not assert that the original geometric image exists. -/
theorem finite_norm_from_image (H C : FrameNorms E)
    (a b k : E) (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : H.finiteNorm w = (w a)⁻¹) (hc : C.finiteNorm w = (w b)⁻¹)
    (image : Submodule.span V ({a^2*k} : Set E) =
      Submodule.span V ({(210:E)*b} : Set E)) :
    w k * C.finiteNorm w / w (210:E) = (H.finiteNorm w)^2 := by
  have c0 : (210:E) ≠ 0 := by norm_num
  obtain ⟨u,h⟩ := primitive_unit w (a^2*k) ((210:E)*b) (mul_ne_zero c0 hb) image
  have eq : (w a)^2 * w k = w (210:E) * w b := by
    calc
      _ = w (a^2*k) := by rw [map_mul, map_pow]
      _ = w ((↑(u:V):E)*((210:E)*b)) := congrArg (fun z : E => w z) h
      _ = _ := by
        rw [map_mul w (↑(u:V):E), unit_norm w u, one_mul, map_mul]
  have p₁ := (FinitePlace.pos_iff (w:=w)).mpr ha
  have p₂ := (FinitePlace.pos_iff (w:=w)).mpr hb
  have p₃ := (FinitePlace.pos_iff (w:=w)).mpr c0
  rw [hc,hd]
  field_simp [p₁.ne',p₂.ne',p₃.ne']
  nlinarith only [eq]

end OriginalExactLocalKSUnit318

#print axioms OriginalExactLocalKSUnit318.unit_norm
#print axioms OriginalExactLocalKSUnit318.primitive_unit
#print axioms OriginalExactLocalKSUnit318.finite_norm_from_image
