module
public import OriginalEliminantLeadingTerm318
public section
noncomputable section
namespace OriginalWholeBasisEliminants318
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalControlledIntegralBasis318
open OriginalWholeBasisCoordinates318 OriginalAffineSieveEliminants318 OriginalEliminantLeadingTerm318
set_option maxHeartbeats 5500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def normCoordinate (coordinate : Bool) (a : Vector ℤ) : ℤ :=
  if coordinate then a.2.1 else a.1
@[expose] def lastHom : Vector ℤ →+ ℤ where
  toFun a := a.2.2
  map_zero' := rfl
  map_add' _ _ := rfl
@[expose] def minorHom (coordinate : Bool) (d : Vector ℤ) : Vector ℤ →+ ℤ where
  toFun a := d.2.2*normCoordinate coordinate a-normCoordinate coordinate d*a.2.2
  map_zero' := by cases coordinate <;> simp [normCoordinate]
  map_add' a b := by cases coordinate <;> simp [normCoordinate] <;> ring

/-- Whole integer spanning detects a nonzero functional on an ORIGINAL
modulus-axis point. This avoids a generic-position assumption on the basis. -/
lemma basis_detects (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple q κ s u v z)
    (φ : Vector ℤ →+ ℤ) (y : Vector ℤ) (hy : y∈literalLattice q κ s)
    (hne : φ y≠0) : ∃ i : Fin 3, φ (![u,v,z] i)≠0 := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨a,b,c,he⟩ := hb.2 y hy
  have h0 : φ u=0 := hn 0
  have h1 : φ v=0 := hn 1
  have h2 : φ z=0 := hn 2
  apply hne
  rw [he]
  simp only [map_add,map_zsmul,h0,h1,h2,smul_zero,add_zero]

/-- One actual basis direction has nonzero w coordinate. For that SAME
direction, each original norm factor has an actual other-basis cross minor
which is nonzero. Directions are selected before all primes. -/
theorem actual_basis_pivot (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (κ : ℤ)
    (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) :
    ∃ i : Fin 3, (![u,v,z] i).2.2≠0 ∧
      ∀ coordinate : Bool, ∃ j : Fin 3, minorHom coordinate (![u,v,z] i) (![u,v,z] j)≠0 := by
  let M : ℤ := FixedSquarefreeCRT318.modulus q
  have hM : M≠0 := by exact_mod_cast (FixedSquarefreeCRT318.modulus_positive q hq).ne'
  have hw : (0,0,M)∈literalLattice q κ s := by
    simpa [M] using modulus_multiple_mem q κ s (0,0,1)
  obtain ⟨i,hi⟩ := basis_detects q κ s u v z hb lastHom (0,0,M) hw hM
  refine ⟨i,hi,?_⟩
  intro coordinate
  let y : Vector ℤ := if coordinate then (0,M,0) else (M,0,0)
  have hy : y∈literalLattice q κ s := by
    cases coordinate
    · simpa [y,M] using modulus_multiple_mem q κ s (1,0,0)
    · simpa [y,M] using modulus_multiple_mem q κ s (0,1,0)
  apply basis_detects q κ s u v z hb (minorHom coordinate (![u,v,z] i)) y hy
  have he : minorHom coordinate (![u,v,z] i) y=(![u,v,z] i).2.2*M := by
    cases coordinate <;> simp [minorHom,normCoordinate,y]
  rw [he]
  exact mul_ne_zero hi hM

@[expose] def lineEliminant (side coordinate : Bool) (κ t : ℤ) (e d : Vector ℤ) : Polynomial ℤ :=
  let dx := normCoordinate coordinate d
  let ex := normCoordinate coordinate e
  if side then
    scaledEliminant (κ*(t+2)*d.2.2^2-2*d.1*d.2.1)
      (2*κ*(t+2)*d.2.2*e.2.2-2*(d.1*e.2.1+e.1*d.2.1))
      (κ*(t+2)*e.2.2^2-2*e.1*e.2.1) 0
      (dx^2) (2*dx*ex) (ex^2) (t^2)
  else scaledEliminant (κ*d.2.2^2) (2*κ*d.2.2*e.2.2) (κ*e.2.2^2) (2*t)
      (dx^2) (2*dx*ex) (ex^2) (t^2)

/-- The polynomial certified nonzero below evaluates to the SAME
integer eliminant used by the actual affine-fiber divisibility theorem. -/
lemma lineEliminant_eval (side coordinate : Bool) (κ t : ℤ) (e d : Vector ℤ) (n : ℤ) :
    (lineEliminant side coordinate κ t e d).eval n=
      normEliminant side κ t (n • e) d coordinate := by
  cases side <;> cases coordinate <;>
    simp [lineEliminant,scaledEliminant,OriginalQuadraticEliminant318.eliminant,
      normEliminant,normCoordinate,fA,fB,fC,LiteralAdjacentNormSlice318.P,
      LiteralAdjacentNormSlice318.P',zsmul_eq_mul] <;> ring

/-- Actual nonzero eliminant producer for BOTH original norm factors and
BOTH regular polynomial pairs, on one actual basis pivot fixed in advance.
The second t=-2 case is deliberately excluded here and must use its exact
linear-factor geometry instead of a false nonzero quartic certificate. -/
theorem actual_regular_eliminants (q : ι → ℕ) (hq : ∀ i, (q i).Prime)
    (κ t : ℤ) (hκ : κ≠0) (ht : t+2≠0)
    (s : ∀ i, Option (ZMod (q i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple q κ s u v z) :
    ∃ i : Fin 3, (![u,v,z] i).2.2≠0 ∧
      ∀ coordinate : Bool, ∃ j : Fin 3,
        lineEliminant false coordinate κ t (![u,v,z] j) (![u,v,z] i)≠0 ∧
        lineEliminant true coordinate κ t (![u,v,z] j) (![u,v,z] i)≠0 := by
  obtain ⟨i,hi,hm⟩ := actual_basis_pivot q hq κ s u v z hb
  refine ⟨i,hi,?_⟩
  intro coordinate
  obtain ⟨j,hj⟩ := hm coordinate
  refine ⟨j,?_,?_⟩
  · exact first_nonzero κ t _ _ _ _ hκ hj
  · apply scaled_nonzero
    cases coordinate
    · rw [second_leading_x]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ ht)) (pow_ne_zero _ hj)
    · rw [second_leading_z]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ ht)) (pow_ne_zero _ hj)

end OriginalWholeBasisEliminants318
