module
public import OriginalOffsetEliminant318
public section
noncomputable section
namespace OriginalShearedOffsetNonzero318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open OriginalWholeBasisEliminants318 OriginalEliminantLeadingTerm318
open OriginalBoundedIntegerShear318 OriginalOffsetEliminant318
set_option maxHeartbeats 6500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every successful bounded shear has a nonzero transverse minor in
one of the SAME two unsheared offset directions. Whole-lattice spanning
at an original modulus-axis point produces it; genericity is not assumed. -/
theorem transverse_minor (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (κ : ℤ)
    (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) (i j : ℤ)
    (hw : (shear i j u v z).2.2≠0) (coordinate : Bool) :
    minorHom coordinate (shear i j u v z) u≠0 ∨
      minorHom coordinate (shear i j u v z) v≠0 := by
  let d := shear i j u v z
  let φ := minorHom coordinate d
  by_contra hn
  push_neg at hn
  have hu : φ u=0 := hn.1
  have hv : φ v=0 := hn.2
  have hself : φ d=0 := by cases coordinate <;> simp [φ,minorHom,normCoordinate,mul_comm]
  have hz : φ z=0 := by
    have he : φ d=φ z+i • φ u+j • φ v := by
      simp only [d,shear,map_add,map_zsmul]
    rw [he,hu,hv,smul_zero,add_zero,add_zero] at hself
    exact hself
  let M : ℤ := FixedSquarefreeCRT318.modulus q
  have hM : M≠0 := by exact_mod_cast (FixedSquarefreeCRT318.modulus_positive q hq).ne'
  let y : Vector ℤ := if coordinate then (0,M,0) else (M,0,0)
  have hy : y∈literalLattice q κ s := by
    cases coordinate
    · simpa [y,M] using modulus_multiple_mem q κ s (1,0,0)
    · simpa [y,M] using modulus_multiple_mem q κ s (0,1,0)
  obtain ⟨a,b,c,he⟩ := hb.2 y hy
  have hy0 : φ y=0 := by rw [he]; simp only [map_add,map_zsmul,hu,hv,hz,smul_zero,add_zero]
  have hvalue : φ y=d.2.2*M := by cases coordinate <;> simp [φ,y,minorHom,normCoordinate]
  rw [hvalue] at hy0
  exact mul_ne_zero hw hM hy0

lemma line_nonzero (side coordinate : Bool) (κ t : ℤ) (hκ : κ≠0)
    (ht : side=true → t+2≠0) (e d : Vector ℤ) (hm : minorHom coordinate d e≠0) :
    lineEliminant side coordinate κ t e d≠0 := by
  cases side
  · exact first_nonzero κ t _ _ _ _ hκ hm
  · apply scaled_nonzero
    cases coordinate
    · rw [second_leading_x]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ (ht rfl))) (pow_ne_zero _ hm)
    · rw [second_leading_z]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ (ht rfl))) (pow_ne_zero _ hm)

/-- BOTH actual remaining-coordinate eliminants are nonzero polynomials
for EVERY shear whose original w coordinate is nonzero. This bridges the
primewise finite-shear producer to zero-locus counting without switching
back to a possibly long pivot. -/
theorem actual_offset_nonzero (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (κ t : ℤ)
    (hκ : κ≠0) (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) (i j : ℤ)
    (hw : (shear i j u v z).2.2≠0) (side coordinate : Bool)
    (ht : side=true → t+2≠0) :
    polynomial side coordinate κ t u v (shear i j u v z)≠0 := by
  obtain hU|hV := transverse_minor q hq κ s u v z hb i j hw coordinate
  · intro hz
    have hh := first_axis side coordinate κ t u v (shear i j u v z)
    rw [hz,map_zero] at hh
    exact line_nonzero side coordinate κ t hκ ht u _ hU hh.symm
  · intro hz
    have hh := second_axis side coordinate κ t u v (shear i j u v z)
    rw [hz,map_zero] at hh
    exact line_nonzero side coordinate κ t hκ ht v _ hV hh.symm

lemma successful_first_nonzero_w (κ t : ℤ) (d : Vector ℤ) (p : ℕ)
    (ha : ¬(p:ℤ)∣OriginalAffineSieveEliminants318.fA false κ t d) : d.2.2≠0 := by
  intro hw
  apply ha
  simp [OriginalAffineSieveEliminants318.fA,hw]

end OriginalShearedOffsetNonzero318
