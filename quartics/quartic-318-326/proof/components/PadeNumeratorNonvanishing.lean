module
public import G4Nonvanishing
public import ConcreteG8Domain
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.Data.ZMod.Basic
public section
namespace PadeNumeratorNonvanishing
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
instance prime19 : Fact (Nat.Prime 19) := ⟨by norm_num⟩
instance prime23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

@[expose] noncomputable def HG : ℤ[X] :=
  X^3 + C 34905*X^2 + C (1280*100776)*X + C (1280^2*69615)
@[expose] noncomputable def HJ : ℤ[X] :=
  X^3 + C 312*X^2 + C (-8*4641)*X + C (64*9945)

theorem degree_G : HG.natDegree=3 := by unfold HG; compute_degree <;> norm_num
theorem degree_J : HJ.natDegree=3 := by unfold HJ; compute_degree <;> norm_num
theorem monic_G : HG.Monic := by unfold HG; monicity!
theorem monic_J : HJ.Monic := by unfold HJ; monicity!

theorem G_mod_no_root (x : ZMod 19) :
    ¬ IsRoot (HG.map (Int.castRingHom (ZMod 19))) x := by
  simp only [HG,IsRoot,eval_map,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  fin_cases x <;> norm_num <;> decide

theorem J_mod_no_root (x : ZMod 23) :
    ¬ IsRoot (HJ.map (Int.castRingHom (ZMod 23))) x := by
  simp only [HJ,IsRoot,eval_map,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  fin_cases x <;> norm_num <;> decide

theorem irreducible_G : Irreducible HG := by
  apply monic_G.irreducible_of_irreducible_map HG (φ := Int.castRingHom (ZMod 19))
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [monic_G.natDegree_map,degree_G]; decide
  · exact G_mod_no_root

theorem irreducible_J : Irreducible HJ := by
  apply monic_J.irreducible_of_irreducible_map HJ (φ := Int.castRingHom (ZMod 23))
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [monic_J.natDegree_map,degree_J]; decide
  · exact J_mod_no_root

@[expose] noncomputable def GQ : ℚ[X] := HG.map (Int.castRingHom ℚ)
@[expose] noncomputable def JQ : ℚ[X] := HJ.map (Int.castRingHom ℚ)

theorem irreducible_GQ : Irreducible GQ :=
 (IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic_G.isPrimitive).mp irreducible_G
theorem irreducible_JQ : Irreducible JQ :=
 (IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic_J.isPrimitive).mp irreducible_J

@[expose] def G {K : Type*} [Field K] (x : K) : K :=
  1-(152/105)*x+(179/357)*x^2-(256/13923)*x^3
@[expose] def J {K : Type*} [Field K] (x : K) : K :=
  1+(7/15)*x+(8/255)*x^2-(8/9945)*x^3

theorem GQ_no_root {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 3) (x : K) :
    aeval x GQ ≠ 0 := by
  intro hx
  have heq := minpoly.eq_of_irreducible_of_monic irreducible_GQ hx (monic_G.map _)
  have hdeg := minpoly.natDegree_le (A := ℚ) x
  rw [←heq,GQ,monic_G.natDegree_map,degree_G] at hdeg
  omega

theorem JQ_no_root {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hdim : Module.finrank ℚ K < 3) (x : K) :
    aeval x JQ ≠ 0 := by
  intro hx
  have heq := minpoly.eq_of_irreducible_of_monic irreducible_JQ hx (monic_J.map _)
  have hdeg := minpoly.natDegree_le (A := ℚ) x
  rw [←heq,JQ,monic_J.natDegree_map,degree_J] at hdeg
  omega

theorem G_scaled_identity {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] (x : K) :
    aeval (-1280*x) GQ = (1280^2*69615 : K)*G x := by
  simp only [GQ,HG,aeval_def,eval₂_map,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  norm_num [G]
  ring

theorem J_scaled_identity {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] (x : K) :
    aeval (-8*x) JQ = (64*9945 : K)*J x := by
  simp only [JQ,HJ,aeval_def,eval₂_map,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  norm_num [J]
  ring

theorem G_nonzero (x : ConcreteG8Domain.K) : G x ≠ 0 := by
  intro hx
  have hn := GQ_no_root (by rw [ConcreteG8Domain.dimension]; decide) (-1280*x)
  rw [G_scaled_identity,hx,mul_zero] at hn
  exact hn rfl

theorem J_nonzero (x : ConcreteG8Domain.K) : J x ≠ 0 := by
  intro hx
  have hn := JQ_no_root (by rw [ConcreteG8Domain.dimension]; decide) (-8*x)
  rw [J_scaled_identity,hx,mul_zero] at hn
  exact hn rfl

end PadeNumeratorNonvanishing
