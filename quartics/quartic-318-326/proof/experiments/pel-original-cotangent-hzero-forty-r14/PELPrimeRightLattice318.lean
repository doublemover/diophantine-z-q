module
public import PELNormalizerParityQuotient318
public section
noncomputable section
namespace PELPrimeRightLattice318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELPrimeNormalizerData318
set_option maxHeartbeats 1600000

instance primeNeZero (i : Fin 4) : NeZero (prime i) :=
  ⟨by fin_cases i <;> norm_num [prime]⟩

@[expose] def conjugateCoefficients : Fin 4 → Coordinates :=
  ![![-10,2,4,-3],![-9,2,3,-3],![-3,0,1,0],![-14,5,7,-7]]

theorem original_conjugate (i : Fin 4) :
    embed (conjugateCoefficients i)=star (element i) := by
  fin_cases i <;> ext <;> norm_num [conjugateCoefficients,element,coefficients,embed]

/-- Exact integer-coordinate multiplication by n and then bar(n). -/
theorem right_norm (i : Fin 4) (a : Coordinates) :
    product (product a (coefficients i)) (conjugateCoefficients i)=
      fun j => (prime i:ℤ)*a j := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [product,coefficients,conjugateCoefficients,prime] <;> ring

theorem left_norm (i : Fin 4) (a : Coordinates) :
    product (product a (conjugateCoefficients i)) (coefficients i)=
      fun j => (prime i:ℤ)*a j := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [product,coefficients,conjugateCoefficients,prime] <;> ring

@[expose] def rows : Fin 4 → Fin 2 → Fin 4 := ![![1,3],![1,3],![0,1],![1,3]]

/-- Two specified coordinates of the ACTUAL right product with bar(n),
reduced at the norm prime. They detect the entire original lattice image. -/
@[expose] def residue (i : Fin 4) (a : Coordinates) : Fin 2 → ZMod (prime i) :=
  fun j => ((product a (conjugateCoefficients i)) (rows i j):ZMod (prime i))

theorem residue_add (i : Fin 4) (a b : Coordinates) :
    residue i (a+b)=residue i a+residue i b := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [residue,rows,product,conjugateCoefficients,prime] <;> ring

theorem residue_zero (i : Fin 4) : residue i 0=0 := by
  ext j
  simp [residue,product]

@[expose] def residueHom (i : Fin 4) : Coordinates →+ (Fin 2 → ZMod (prime i)) where
  toFun := residue i
  map_zero' := residue_zero i
  map_add' := residue_add i

/-- The omitted coordinates really are divisible by p, using the two
specified residue equations. No rank-of-a-matrix shortcut is used. -/
theorem all_divisible (i : Fin 4) (a : Coordinates) (h : residue i a=0) :
    ∀ j : Fin 4,(prime i:ℤ)∣(product a (conjugateCoefficients i)) j := by
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((product a (conjugateCoefficients i)) (rows i 0)) (prime i)).mp (congrFun h 0)
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((product a (conjugateCoefficients i)) (rows i 1)) (prime i)).mp (congrFun h 1)
  intro j
  fin_cases i <;> fin_cases j <;>
    norm_num [prime,product,conjugateCoefficients,rows] at h0 h1 ⊢ <;> omega

/-- Actual integral preimages are reconstructed from the divisibility of
x*bar(n); the theorem covers every original integer-coordinate vector. -/
theorem kernel_preimage (i : Fin 4) (a : Coordinates) (h : residue i a=0) :
    ∃ b : Coordinates,product b (coefficients i)=a := by
  choose b hb using all_divisible i a h
  refine ⟨b,?_⟩
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [prime,product,coefficients,conjugateCoefficients] at h0 h1 h2 h3 ⊢ <;> omega

theorem image_zero (i : Fin 4) (b : Coordinates) :
    residue i (product b (coefficients i))=0 := by
  ext j
  simp only [residue,right_norm,Int.cast_mul,Pi.zero_apply]
  simp

theorem kernel_iff (i : Fin 4) (a : Coordinates) :
    residue i a=0 ↔ ∃ b : Coordinates,product b (coefficients i)=a := by
  constructor
  · exact kernel_preimage i a
  · rintro ⟨b,rfl⟩
    exact image_zero i b
end PELPrimeRightLattice318
