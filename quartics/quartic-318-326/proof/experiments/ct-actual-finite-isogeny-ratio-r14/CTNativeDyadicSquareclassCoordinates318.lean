module
public import CTNativePadicValuationBit318
public import OriginalCasselsDyadicNormalize318
import all CTNativePadicUnitNormalization318
import all CTNativePadicValuationBit318
import Mathlib.Tactic.NormNum
public section

noncomputable section
namespace CTNativeDyadicSquareclassCoordinates318

open CTNativePadicValuationBit318 CTNativePadicUnitNormalization318
open ActualTwoDescentSquareClassQuotient318 OriginalCasselsDyadicNormalize318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- epsilon(u)=(u-1)/2 mod 2 for all actual odd residues. -/
def epsilonBit (u : ZMod 8) : Bit := if u=3 ∨ u=7 then 1 else 0

/-- omega(u)=(u²-1)/8 mod 2 for all actual odd residues. -/
def omegaBit (u : ZMod 8) : Bit := if u=3 ∨ u=5 then 1 else 0

private theorem unit_coprime (u : ZMod 8) (h : IsUnit u) : Nat.Coprime u.val 8 :=
  (ZMod.isUnit_iff_coprime _ 8).mp (by simpa only [ZMod.natCast_zmod_val] using h)

private theorem unitBits_mul (u v : ZMod 8) (hu : IsUnit u) (hv : IsUnit v) :
    epsilonBit (u*v)=epsilonBit u+epsilonBit v ∧
    omegaBit (u*v)=omegaBit u+omegaBit v := by
  have h : ∀ a b : Fin 8, Nat.Coprime a.val 8 → Nat.Coprime b.val 8 →
      epsilonBit ((a.val:ZMod 8)*b.val)=epsilonBit a.val+epsilonBit b.val ∧
      omegaBit ((a.val:ZMod 8)*b.val)=omegaBit a.val+omegaBit b.val := by decide
  simpa only [ZMod.natCast_zmod_val] using h
    ⟨u.val,ZMod.val_lt u⟩ ⟨v.val,ZMod.val_lt v⟩ (unit_coprime u hu) (unit_coprime v hv)

private theorem unitBits_zero_to_one (u : ZMod 8) (hu : IsUnit u)
    (hε : epsilonBit u=0) (hω : omegaBit u=0) : u=1 := by
  have h : ∀ a : Fin 8, Nat.Coprime a.val 8 →
      epsilonBit a.val=0 → omegaBit a.val=0 → (a.val:ZMod 8)=1 := by decide
  have k := h ⟨u.val,ZMod.val_lt u⟩ (unit_coprime u hu)
  simp only [ZMod.natCast_zmod_val] at k
  exact k hε hω

def twoResidueUnits : ℚ_[2]ˣ →* (ZMod 8)ˣ :=
  (Units.map res8.toMonoidHom).comp (normalizeHom 2)

def dyadicUnitCoordinates : ℚ_[2]ˣ →* Multiplicative (Bit × Bit × Bit) where
  toFun u := Multiplicative.ofAdd ((valuationBit 2 u).toAdd,
    epsilonBit (twoResidueUnits u:ZMod 8),omegaBit (twoResidueUnits u:ZMod 8))
  map_one' := by
    change ((valuationBit 2 1).toAdd,epsilonBit (twoResidueUnits 1:ZMod 8),
      omegaBit (twoResidueUnits 1:ZMod 8))=(0,0,0)
    rw [map_one (valuationBit 2),map_one twoResidueUnits,Units.val_one] <;> decide
  map_mul' x y := by
    change ((valuationBit 2 (x*y)).toAdd,epsilonBit (twoResidueUnits (x*y):ZMod 8),
      omegaBit (twoResidueUnits (x*y):ZMod 8)) =
      ((valuationBit 2 x).toAdd,epsilonBit (twoResidueUnits x:ZMod 8),
        omegaBit (twoResidueUnits x:ZMod 8)) +
      ((valuationBit 2 y).toAdd,epsilonBit (twoResidueUnits y:ZMod 8),
        omegaBit (twoResidueUnits y:ZMod 8))
    rw [map_mul (valuationBit 2),map_mul twoResidueUnits,Units.val_mul]
    have h := unitBits_mul (twoResidueUnits x) (twoResidueUnits y)
      (twoResidueUnits x).isUnit (twoResidueUnits y).isUnit
    exact Prod.ext rfl (Prod.ext h.1 h.2)

def dyadicCoordinates : SquareClass ℚ_[2] →* Multiplicative (Bit × Bit × Bit) :=
  liftBitCoordinates 2 dyadicUnitCoordinates

theorem normalized_res8_value (u : ℚ_[2]ˣ) :
    (twoResidueUnits u:ZMod 8)=res8 (normalizedInteger 2 u) := by
  change res8 (↑(normalizedUnit 2 u):ℤ_[2])= _
  exact congrArg res8 (normalizedIntegralUnit 2 u).unit_spec

theorem dyadic_value_coords (x : ℚ_[2]) (hx : x≠0) :
    (dyadicCoordinates (classOf x hx)).toAdd =
      ((x.valuation:Bit),
        epsilonBit (res8 (normalizedInteger 2 (Units.mk0 x hx))),
        omegaBit (res8 (normalizedInteger 2 (Units.mk0 x hx)))) := by
  rw [dyadicCoordinates,liftBitCoordinates_on_value]
  change ((x.valuation:Bit),epsilonBit (twoResidueUnits (Units.mk0 x hx):ZMod 8),
    omegaBit (twoResidueUnits (Units.mk0 x hx):ZMod 8))=_
  rw [normalized_res8_value]

theorem dyadicCoordinates_injective : Function.Injective dyadicCoordinates := by
  apply coordinates_injective_of_kernel_square
  intro x hx he
  let u := Units.mk0 x hx
  let U := normalizedInteger 2 u
  have h := congrArg Multiplicative.toAdd he
  rw [dyadic_value_coords] at h
  have hV : (x.valuation:Bit)=0 := congrArg Prod.fst h
  have hε : epsilonBit (res8 U)=0 := congrArg (fun k : Bit × Bit × Bit => k.2.1) h
  have hω : omegaBit (res8 U)=0 := congrArg (fun k : Bit × Bit × Bit => k.2.2) h
  have hU := normalizedIntegralUnit 2 u
  have h1 := unitBits_zero_to_one (res8 U) (hU.map res8) hε hω
  obtain ⟨r,hr,hR⟩ := square_of_res8_one U h1
  exact square_of_valuationBit_zero_and_norm_square 2 x hx hV r hr hR.symm

theorem dyadic_coords_of_integral_unit (U : ℤ_[2]) (hU : IsUnit U) :
    (dyadicCoordinates (classOf (U:ℚ_[2]) (PadicInt.coe_ne_zero.mpr hU.ne_zero))).toAdd =
      (0,epsilonBit (res8 U),omegaBit (res8 U)) := by
  have hV := val_of_unit U hU
  have hN := normalizedInteger_valuative_unit 2
    (Units.mk0 (U:ℚ_[2]) (PadicInt.coe_ne_zero.mpr hU.ne_zero)) U rfl hV
  rw [dyadic_value_coords,hV,Int.cast_zero,hN]

theorem dyadic_coords_prime :
    (dyadicCoordinates (classOf ((2:ℕ):ℚ_[2]) (padic_prime_ne 2))).toAdd=(1,0,0) := by
  rw [dyadic_value_coords,Padic.valuation_p,Int.cast_one,normalizedInteger_prime 2,map_one] <;> decide

theorem dyadic_coords_five :
    (dyadicCoordinates (classOf (5:ℚ_[2]) (by norm_num))).toAdd=(0,0,1) := by
  have hU : IsUnit (5:ℤ_[2]) := unit_of_mod2_one _ (by rw [map_ofNat] <;> decide)
  have H := dyadic_coords_of_integral_unit (5:ℤ_[2]) hU
  have hcoe : ((5:ℤ_[2]):ℚ_[2])=(5:ℚ_[2]) := by
    change PadicInt.Coe.ringHom (5:ℤ_[2])=5
    rw [map_ofNat]
  have hR : res8 (5:ℤ_[2])=5 := by rw [map_ofNat]
  rw [hR] at H
  -- Proof irrelevance for the same nonzero representative, after its exact coercion.
  have he : classOf ((5:ℤ_[2]):ℚ_[2]) (PadicInt.coe_ne_zero.mpr hU.ne_zero) =
      classOf (5:ℚ_[2]) (by norm_num) :=
    (class_of_eq_iff _ _ _ _).mpr ⟨1,one_ne_zero,by simpa only [one_pow,mul_one] using hcoe⟩
  rw [he] at H
  simpa only [show epsilonBit (5:ZMod 8)=0 by decide,
    show omegaBit (5:ZMod 8)=1 by decide] using H

end CTNativeDyadicSquareclassCoordinates318

#print axioms CTNativeDyadicSquareclassCoordinates318.dyadicCoordinates_injective
