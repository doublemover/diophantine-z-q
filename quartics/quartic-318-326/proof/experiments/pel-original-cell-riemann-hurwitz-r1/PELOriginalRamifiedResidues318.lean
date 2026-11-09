module
public import PELPositiveNormalizerNormalForm318
public section
noncomputable section
namespace PELOriginalRamifiedResidues318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELPrimeRightLattice318
set_option maxHeartbeats 1800000

@[expose] def quadraticA (i : Fin 4) : ZMod (prime i) := ![1,1,3,1] i
@[expose] def quadraticB (i : Fin 4) : ZMod (prime i) := ![1,1,0,1] i
abbrev Residue (i : Fin 4) := QuadraticAlgebra (ZMod (prime i)) (quadraticA i) (quadraticB i)

instance no_root (i : Fin 4) : Fact (∀ r : ZMod (prime i),r^2≠quadraticA i+quadraticB i*r) := ⟨by
  have h2 : ∀ r : ZMod 2,r^2≠1+r := by intro r; fin_cases r <;> decide
  have h3 : ∀ r : ZMod 3,r^2≠1+r := by intro r; fin_cases r <;> decide
  have h5 : ∀ r : ZMod 5,r^2≠3 := by intro r; fin_cases r <;> decide
  have h7 : ∀ r : ZMod 7,r^2≠1+r := by intro r; fin_cases r <;> decide
  fin_cases i
  · simpa [prime,quadraticA,quadraticB] using h2
  · simpa [prime,quadraticA,quadraticB] using h3
  · simpa [prime,quadraticA,quadraticB] using h5
  · simpa [prime,quadraticA,quadraticB] using h7⟩

/-- The residue coordinates are expressed in the SAME original half-integral
order basis. At5 the surviving generator is e3, not the nilpotent j direction. -/
@[expose] def reduceCoordinates (i : Fin 4) (a : Coordinates) : Residue i :=
  if i=2 then ⟨((a 0+3*a 2:ℤ):ZMod (prime i)),(a 3:ZMod (prime i))⟩
  else ⟨(a 0:ZMod (prime i)),(a 2:ZMod (prime i))⟩

theorem reduce_add (i : Fin 4) (a b : Coordinates) :
    reduceCoordinates i (a+b)=reduceCoordinates i a+reduceCoordinates i b := by
  fin_cases i <;> ext <;> simp [reduceCoordinates,prime] <;> ring

theorem reduce_product (i : Fin 4) (a b : Coordinates) :
    reduceCoordinates i (product a b)=reduceCoordinates i a*reduceCoordinates i b := by
  fin_cases i <;> ext <;>
    simp [reduceCoordinates,product,prime,quadraticA,quadraticB] <;> push_cast <;> norm_num <;> ring

/-- Genuine ring maps from the original order to the four residue FIELDS,
not additive identifications with equally sized sets. -/
@[expose] def reduction (i : Fin 4) : order →+* Residue i where
  toFun x := reduceCoordinates i (coordinatesEquiv.symm x)
  map_zero' := by fin_cases i <;> ext <;> simp [reduceCoordinates]
  map_one' := by
    rw [←PELOrderReductionThree318.coordinates_one]
    fin_cases i <;> ext <;> simp [reduceCoordinates]
  map_add' x y := by rw [map_add]; exact reduce_add i _ _
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
    obtain ⟨b,rfl⟩ := coordinatesEquiv.surjective y
    rw [←PELOrderReductionThree318.coordinates_mul]
    simpa only [AddEquiv.symm_apply_apply] using reduce_product i a b

theorem reduction_coordinates (i : Fin 4) (a : Coordinates) :
    reduction i (coordinatesEquiv a)=reduceCoordinates i a := by simp [reduction]

theorem reduction_surjective (i : Fin 4) : Function.Surjective (reduction i) := by
  intro x
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective x.re
  obtain ⟨b,hb⟩ := ZMod.intCast_surjective x.im
  by_cases hi : i=2
  · refine ⟨coordinatesEquiv ![a,0,0,b],?_⟩
    rw [reduction_coordinates]
    ext <;> simp [reduceCoordinates,hi,ha,hb]
  · refine ⟨coordinatesEquiv ![a,0,b,0],?_⟩
    rw [reduction_coordinates]
    ext <;> simp [reduceCoordinates,hi,ha,hb]

noncomputable instance residueFintype (i : Fin 4) : Fintype (Residue i) :=
  Fintype.ofEquiv (ZMod (prime i)×ZMod (prime i)) (QuadraticAlgebra.equivProd _ _).symm

noncomputable instance residueField (i : Fin 4) : Field (Residue i) := inferInstance

theorem residue_card (i : Fin 4) : Nat.card (Residue i)=(prime i)^2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _)]
  simp [Nat.card_eq_fintype_card,pow_two]
end PELOriginalRamifiedResidues318
