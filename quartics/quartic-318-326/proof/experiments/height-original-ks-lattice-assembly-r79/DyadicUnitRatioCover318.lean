module
public import MonicRootEtale318
public section
noncomputable section
namespace DyadicUnitRatioCover318
open Polynomial
variable {R : Type*} [CommRing R]

/-- The integral half-coordinate satisfies h²+h=c, not h²=1+4c.
No denominator 2 is required in the coefficient ring. -/
@[expose] def equation (c : R) : R[X] := X^2+(X-C c)
abbrev Cover (c : R) := AdjoinRoot (equation c)

theorem monic (c : R) : (equation c).Monic := by
  apply Polynomial.monic_X_pow_add
  calc
    degree (X-C c) ≤ max (degree (X : R[X])) (degree (C c)) := degree_sub_le _ _
    _ ≤ 1 := max_le degree_X_le (le_trans degree_C_le (by decide))
    _ < (2 : WithBot ℕ) := by decide

theorem degree_two [Nontrivial R] (c : R) : (equation c).natDegree=2 := by
  unfold equation
  compute_degree!

theorem bezout (c : R) :
    (-4)*equation c + (2*X+1)*(equation c).derivative = C (1+4*c) := by
  simp [equation,derivative_pow] <;> ring

theorem separable (c : R) (hu : IsUnit (1+4*c)) : (equation c).Separable := by
  obtain ⟨u,hu⟩ := hu
  refine ⟨C (↑u⁻¹ : R)*(-4), C (↑u⁻¹ : R)*(2*X+1), ?_⟩
  rw [mul_assoc,mul_assoc,←mul_add,bezout,←hu,←C_mul,Units.inv_mul,C_1]

theorem finite (c : R) : Module.Finite R (Cover c) := (monic c).finite_adjoinRoot
theorem free (c : R) : Module.Free R (Cover c) := (monic c).free_adjoinRoot
theorem rank_two [Nontrivial R] (c : R) : Module.finrank R (Cover c)=2 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' (monic c)).basis,Fintype.card_fin]
  exact degree_two c

theorem etale (c : R) (hu : IsUnit (1+4*c)) : Algebra.Etale R (Cover c) :=
  MonicRootEtale318.root_etale _ (monic c) (separable c hu)

theorem faithfullyFlat [Nontrivial R] (c : R) : Module.FaithfullyFlat R (Cover c) :=
  MonicRootEtale318.root_faithfullyFlat _ (monic c) (by rw [degree_two]; decide)

@[expose] def half (c : R) : Cover c := AdjoinRoot.root (equation c)

theorem half_relation (c : R) : half c ^ 2 + half c = algebraMap R (Cover c) c := by
  have h := AdjoinRoot.mk_self (f:=equation c)
  change AdjoinRoot.mk (equation c) (X^2+(X-C c))=0 at h
  rw [map_add,map_pow,AdjoinRoot.mk_X,map_sub,AdjoinRoot.mk_X,AdjoinRoot.mk_C] at h
  change half c ^ 2 + (half c - algebraMap R (Cover c) c) = 0 at h
  linear_combination h

@[expose] def multiplier (c : R) : Cover c := 1+2*half c
theorem multiplier_square (c : R) : multiplier c ^ 2 = algebraMap R (Cover c) (1+4*c) := by
  simp only [multiplier,map_add,map_one,map_mul,map_ofNat]
  linear_combination 4 * half_relation c

theorem multiplier_isUnit (c : R) (hu : IsUnit (1+4*c)) : IsUnit (multiplier c) := by
  apply (isUnit_pow_iff (by decide : 2≠0)).mp
  rw [multiplier_square]
  exact hu.map (algebraMap R (Cover c))
end DyadicUnitRatioCover318
