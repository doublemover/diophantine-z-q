module
public import CTContinuousFieldHTwo318
public import CTQuadraticCarrySwapAlgebra318
import all Mathlib.FieldTheory.AbsoluteGaloisGroup
import all CTFieldPrimitiveRestriction318
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public section
noncomputable section

namespace CTActualQuadraticRootSigns318

open CTFieldPrimitiveRestriction318 CTActualKrullCoordinateOrbit318
open CTQuadraticCarrySwapAlgebra318
open CategoryTheory

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "G" => Gal K
local notation "V" => FieldUnitRep K
local instance : DecidableEq A := Classical.decEq _

/-- Algebraic action on a coordinate, while the domain retains
the actual absolute Krull topology. -/
@[expose] def act (g : G) : A ≃ₐ[K] A := g

theorem act_mul (g h : G) (u : A) :
    act K (g*h) u = act K g (act K h u) := rfl

@[expose] def fieldSign (b : Bool) (u : A) : A := if b then -u else u

def phase (r : Aˣ) (g : G) : Bool :=
  if act K g (r : A) = (r : A) then false else true

theorem phase_lc (r : Aˣ) : IsLocallyConstant (phase K r) :=
  (field_coordinate_locally_constant (r : A)).comp
    (fun u : A => if u = (r : A) then false else true)

private theorem neg_root_ne_root (r : Aˣ) : -(r : A) ≠ (r : A) := by
  intro h
  have hh : (2 : A)*(r : A)=0 := calc
    _ = (r:A)+(r:A) := two_mul _
    _ = -(r:A)+(r:A) := congrArg (fun t : A => t+(r:A)) h.symm
    _ = 0 := neg_add_cancel _
  exact (mul_ne_zero (by norm_num) r.ne_zero) hh

private theorem phase_of_value (r : Aˣ) (g : G) (b : Bool)
    (hb : act K g (r : A) = fieldSign K b (r : A)) : phase K r g = b := by
  cases b
  · have h : act K g (r : A) = (r : A) := hb
    simp [phase,h]
  · have h : act K g (r : A) ≠ (r : A) :=
      fun he => neg_root_ne_root K r (hb.symm.trans he)
    simp [phase,h]

def scalar (a : Kˣ) : V := Additive.ofMul (Units.map (algebraMap K A).toMonoidHom a)

abbrev root (r : Aˣ) : V := Additive.ofMul r

def signUnit : V := Additive.ofMul (-1 : Aˣ)

theorem signUnit_double : signUnit K + signUnit K = 0 := by
  apply Additive.toMul.injective
  apply Units.ext
  change (-1 : A)*(-1)=1
  ring

theorem action_on_value (g : G) (z : V) :
    (((V.ρ g z).toMul : Aˣ) : A) = act K g (z.toMul : A) := by
  change ((((Rep.ofAlgebraAutOnUnits K A).ρ g z).toMul : Aˣ) : A) = _
  simp only [Rep.ofAlgebraAutOnUnits,Rep.ofMulDistribMulAction_ρ_apply_apply,
    AlgEquiv.smul_units_def,Units.coe_map,MonoidHom.coe_ofClass,act] <;> rfl

theorem scalar_fixed (a : Kˣ) (g : G) : V.ρ g (scalar K a) = scalar K a := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [action_on_value]
  change act K g (algebraMap K A (a : K)) = algebraMap K A (a : K)
  exact (act K g).commutes (a : K)

theorem signUnit_fixed (g : G) : V.ρ g (signUnit K) = signUnit K := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [action_on_value]
  change act K g (-1 : A) = -1
  rw [map_neg,map_one]

theorem root_double (r : Aˣ) (a : Kˣ) (hr : (r:A)^2 = algebraMap K A (a : K)) :
    root K r + root K r = scalar K a := by
  apply Additive.toMul.injective
  apply Units.ext
  change (r:A)*(r:A)=algebraMap K A (a : K)
  exact (pow_two (r:A)).symm.trans hr

theorem act_on_square_root (r : Aˣ) (a : Kˣ)
    (hr : (r:A)^2 = algebraMap K A (a : K)) (g : G) :
    act K g (r : A) = fieldSign K (phase K r g) (r : A) := by
  by_cases h : act K g (r : A) = (r : A)
  · simp [phase,fieldSign,h]
  have hS : (act K g (r : A))^2 = (r:A)^2 := calc
    _ = act K g ((r:A)^2) := (map_pow (act K g) (r : A) 2).symm
    _ = algebraMap K A (a : K) := by rw [hr,(act K g).commutes]
    _ = _ := hr.symm
  have hP : (act K g (r : A)-(r:A))*(act K g (r : A)+(r:A))=0 := by
    calc
      _ = (act K g (r : A))^2 - (r:A)^2 := by ring
      _ = 0 := sub_eq_zero.mpr hS
  have hAdd := (mul_eq_zero.mp hP).resolve_left (sub_ne_zero.mpr h)
  have hNeg : act K g (r : A) = -(r:A) :=
    sub_eq_zero.mp (by simpa only [sub_neg_eq_add] using hAdd)
  simpa only [phase,if_neg h,fieldSign] using hNeg

theorem phase_mul (r : Aˣ) (a : Kˣ)
    (hr : (r:A)^2 = algebraMap K A (a : K)) (g h : G) :
    phase K r (g*h) = xor (phase K r g) (phase K r h) := by
  apply phase_of_value
  rw [act_mul, act_on_square_root K r a hr h]
  have hg := act_on_square_root K r a hr g
  cases h1 : phase K r g <;> cases h2 : phase K r h <;>
    simp [h1,h2,fieldSign,xor] at hg ⊢ <;>
    simp [hg,map_neg]

theorem phase_action (r : Aˣ) (a : Kˣ)
    (hr : (r:A)^2 = algebraMap K A (a : K)) (g : G) :
    V.ρ g (root K r) = root K r + mask (phase K r g) (signUnit K) := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [action_on_value,act_on_square_root K r a hr]
  cases h : phase K r g
  · change fieldSign K false (r:A) = (r:A)*1
    rw [mul_one] <;> rfl
  · change fieldSign K true (r:A) = (r:A)*(-1)
    rw [mul_neg,mul_one] <;> rfl

theorem exists_unit_root (a : Kˣ) : ∃ r : Aˣ, (r:A)^2 = algebraMap K A (a : K) := by
  obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K A (a : K)) (by decide : 0 < (2 : ℕ))
  have hne : r ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : (2:ℕ) ≠ 0)] at hr
    exact (map_ne_zero (algebraMap K A) a.ne_zero) hr.symm
  exact ⟨Units.mk0 r hne,hr⟩

/-- A true nonsquare gives a nontrivial sign on the actual absolute
group, not merely a formal two-element target. -/
theorem phase_nontrivial (r : Aˣ) (a : Kˣ)
    (hr : (r:A)^2 = algebraMap K A (a : K)) (ha : ¬IsSquare (a : K)) :
    ∃ g : G, phase K r g = true := by
  classical
  by_contra h
  have hfix (g : (A ≃ₐ[K] A)) : g (r : A) = (r : A) := by
    have hp := act_on_square_root K r a hr (show G from g)
    cases he : phase K r (show G from g)
    · simpa only [he,fieldSign,act] using hp
    · exact False.elim (h ⟨(show G from g),he⟩)
  obtain ⟨z,hz⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (r : A)).2 hfix
  have hz2 : z ^ (2 : ℕ) = (a : K) := (algebraMap K A).injective (by
    rw [map_pow,hz,hr])
  exact ha ⟨z,by simpa only [pow_two] using hz2.symm⟩


end CTActualQuadraticRootSigns318
