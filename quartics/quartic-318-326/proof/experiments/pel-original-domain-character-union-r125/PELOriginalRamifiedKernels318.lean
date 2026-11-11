module
public import PELOriginalRamifiedResidues318
public section
noncomputable section
namespace PELOriginalRamifiedKernels318
open PELPrincipalOrderCoordinates318 PELPrimeNormalizerData318 PELPrimeRightLattice318
open PELOriginalRamifiedResidues318 PELPrimeLatticeResidues318
set_option maxHeartbeats 1800000

@[expose] def divisibility (i : Fin 4) (a : Coordinates) : Prop :=
  if i=2 then (prime i:ℤ)∣a 0+3*a 2 ∧ (prime i:ℤ)∣a 3
  else (prime i:ℤ)∣a 0 ∧ (prime i:ℤ)∣a 2

theorem reduction_zero_iff (i : Fin 4) (a : Coordinates) :
    reduceCoordinates i a=0 ↔ divisibility i a := by
  have hc : reduceCoordinates i a=0 ↔
      (reduceCoordinates i a).re=0 ∧ (reduceCoordinates i a).im=0 := by
    constructor
    · intro h; exact ⟨congrArg QuadraticAlgebra.re h,congrArg QuadraticAlgebra.im h⟩
    · rintro ⟨hr,hi⟩; ext <;> assumption
  rw [hc]
  fin_cases i <;>
    simp [reduceCoordinates,divisibility,prime,ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The new field residue kernel is EXACTLY the old actual prime-normalizer
right lattice kernel; all four original primes and all integer signs are covered. -/
theorem residue_zero_iff (i : Fin 4) (a : Coordinates) :
    residue i a=0 ↔ divisibility i a := by
  constructor
  · intro h
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((product a (conjugateCoefficients i)) (rows i 0)) (prime i)).mp (congrFun h 0)
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((product a (conjugateCoefficients i)) (rows i 1)) (prime i)).mp (congrFun h 1)
    fin_cases i <;>
      norm_num [divisibility,prime,product,conjugateCoefficients,rows] at h0 h1 ⊢ <;> omega
  · intro h
    ext j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (prime i)).mpr
    fin_cases i <;> fin_cases j <;>
      norm_num [divisibility,prime,residue,product,conjugateCoefficients,rows] at h ⊢ <;> omega

theorem actual_kernel (i : Fin 4) :
    (reduction i).toAddMonoidHom.ker=(rightMultiply i).range := by
  rw [←kernel_eq_range]
  ext x
  obtain ⟨a,rfl⟩ := coordinatesEquiv.surjective x
  change reduction i (coordinatesEquiv a)=0 ↔ orderResidue i (coordinatesEquiv a)=0
  rw [reduction_coordinates,orderResidue_coordinates,reduction_zero_iff,residue_zero_iff]

@[expose] def moduloRadical (i : Fin 4) : RingCon order := RingCon.ker (reduction i)
abbrev ResidueQuotient (i : Fin 4) := (moduloRadical i).Quotient

/-- Actual quotient RING equivalence, carrying every original order element
to its specified field residue, not merely an index or cardinality argument. -/
@[expose] def residueEquiv (i : Fin 4) : ResidueQuotient i ≃+* Residue i :=
  RingCon.quotientKerEquivOfSurjective (reduction i) (reduction_surjective i)

theorem residueEquiv_mk (i : Fin 4) (x : order) :
    residueEquiv i ((moduloRadical i).mk' x)=reduction i x := rfl

theorem quotient_card (i : Fin 4) : Nat.card (ResidueQuotient i)=(prime i)^2 := by
  rw [Nat.card_congr (residueEquiv i).toEquiv]
  exact residue_card i
end PELOriginalRamifiedKernels318
