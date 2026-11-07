module
public import AbsoluteHeightNormalization318
public import Mathlib.Algebra.FiniteSupport.Basic
public section
noncomputable section
open NumberField ConcreteG8Domain Polynomial HeightCoverageFromMahler318 ActualQuadraticEmbeddings318
namespace PrimitiveQuadraticMahler318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

lemma root_coefficients (a : ℕ) (b c : ℤ) (u v : ℚ) (hv : v≠0)
    (hr : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0) :
    (b:ℚ) = -2*(a:ℚ)*u ∧ (c:ℚ)=(a:ℚ)*(u^2-2*v^2) := by
  have hre := congrArg QuadraticAlgebra.re hr
  have him := congrArg QuadraticAlgebra.im hr
  norm_num [pair,pow_succ] at hre him
  have hl : 2*(a:ℚ)*u+(b:ℚ)=0 := by
    apply (mul_eq_zero.mp (show v*(2*(a:ℚ)*u+(b:ℚ))=0 by linear_combination him)).resolve_left hv
  constructor
  · linear_combination hl
  · linear_combination hre-u*hl

lemma root_factorization (a : ℕ) (b c : ℤ) (u v : ℚ) (hv : v≠0)
    (hr : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0) :
    (quadratic a b c).map (Int.castRingHom K)=
      C (a:K)*((X-C (pair u v))*(X-C (pair u (-v)))) := by
  obtain ⟨hb,hc⟩ := root_coefficients a b c u v hv hr
  have hBK : (b:K)= -(a:K)*(pair u v+pair u (-v)) := by
    ext <;> simp [pair]
    linear_combination hb
  have hCK : (c:K)=(a:K)*pair u v*pair u (-v) := by
    ext <;> simp [pair]
    · linear_combination hc
    · ring
  simp only [quadratic,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_C,Polynomial.map_X,Int.coe_castRingHom,Int.cast_natCast,hBK,hCK,
    map_neg,map_add,map_mul]
  ring

lemma finite_part_primitive [NumberField K] (a : ℕ) (b c : ℤ) (u v : ℚ)
    (ha : 1≤a) (hv : v≠0) (hg : Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1)
    (hr : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0) :
    (∏ᶠ w : FinitePlace K, max (w (pair u v)) 1)=(a:ℝ) := by
  have haK : (a:K)≠0 := by exact_mod_cast (by omega : a≠0)
  have haR : (a:ℝ)≠0 := by exact_mod_cast (by omega : a≠0)
  have hfac := root_factorization a b c u v hv hr
  have hh : (∏ᶠw : FinitePlace K,
      w (a:K)*max (w (pair u v)) 1*max (w (pair u (-v))) 1)=1 := by
    simp_rw [LocalMahlerHeight.finite_roots_product _ a b c _ _ hg hfac]
    exact finprod_one
  have hab : Function.HasFiniteMulSupport (fun w : FinitePlace K => w (a:K)*max (w (pair u v)) 1) := by
    exact (FinitePlace.hasFiniteMulSupport haK).mul (FiniteHeightEquiv.finite_max_support (pair u v))
  rw [finprod_mul_distrib hab (FiniteHeightEquiv.finite_max_support (pair u (-v))),
    finprod_mul_distrib (FinitePlace.hasFiniteMulSupport haK) (FiniteHeightEquiv.finite_max_support (pair u v)),
    FinitePlace.prod_eq_inv_abs_norm haK,Algebra.norm_natCast,ConcreteG8Domain.dimension] at hh
  have he : starRingAut (pair u v)=pair u (-v) := by ext <;> simp [pair,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star]
  have hconj := FiniteHeightEquiv.finite_part_equiv (starRingAut : K≃+*K) (pair u v)
  rw [he] at hconj
  rw [hconj] at hh
  have hn : ((|(a:ℚ)^2|⁻¹:ℚ):ℝ)=((a:ℝ)^2)⁻¹ := by simp [abs_of_nonneg (sq_nonneg (a:ℚ))]
  rw [hn] at hh
  field_simp at hh
  have hpos : 1≤∏ᶠw : FinitePlace K,max (w (pair u v)) 1 := one_le_finprod (fun _ => le_max_right _ _)
  have haRpos : (0:ℝ)<a := by exact_mod_cast (by omega : 0<a)
  nlinarith

lemma mahler_eq_relative_height [NumberField K] (a : ℕ) (b c : ℤ) (u v : ℚ)
    (ha : 1≤a) (hv : v≠0) (hg : Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1)
    (hr : (a:K)*(pair u v)^2+(b:K)*(pair u v)+(c:K)=0) :
    ((quadratic a b c).map (Int.castRingHom ℂ)).mahlerMeasure=Height.mulHeight₁ (pair u v) := by
  have hfac := congrArg (Polynomial.map positiveComplex) (root_factorization a b c u v hv hr)
  simp only [Polynomial.map_map,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    map_natCast] at hfac
  have hcast : positiveComplex.comp (Int.castRingHom K)=Int.castRingHom ℂ := by ext; simp
  rw [hcast,Polynomial.map_natCast] at hfac
  rw [←Polynomial.C_eq_natCast] at hfac
  rw [hfac,Polynomial.mahlerMeasure_mul,Polynomial.mahlerMeasure_mul,
    Polynomial.mahlerMeasure_const,Polynomial.mahlerMeasure_X_sub_C,Polynomial.mahlerMeasure_X_sub_C,
    NumberField.mulHeight₁_eq,infinite_part_pair,finite_part_primitive a b c u v ha hv hg hr]
  dsimp only [positiveComplex,RingHom.coe_comp,Function.comp_apply]
  change ‖(a:ℂ)‖ * (max 1 ‖(positiveEmbedding (pair u v):ℂ)‖ *
    max 1 ‖(positiveEmbedding (pair u (-v)):ℂ)‖) = _
  simp only [norm_natCast,Complex.norm_real,Real.norm_eq_abs,positiveEmbedding,realEmbedding_pair,
    Rat.cast_neg,neg_mul,←sub_eq_add_neg]
  rw [max_comm 1,max_comm 1]
  ring

theorem primitive_height_identity : HeightCoverageFromMahler318.PrimitiveHeightIdentity := by
  letI : NumberField K := {}
  intro u v hv a b c ha hg hr
  rw [AbsoluteHeightNormalization318.exp_twice_absLogHeight_pair u v hv]
  exact mahler_eq_relative_height a b c u v ha hv hg hr

theorem polynomial_height_coverage : PolynomialHeightInterface318.PolynomialHeightCoverage :=
  HeightCoverageFromMahler318.polynomial_height_coverage_of_height_identity primitive_height_identity

#print axioms root_coefficients
#print axioms root_factorization
#print axioms finite_part_primitive
#print axioms mahler_eq_relative_height
#print axioms primitive_height_identity
#print axioms polynomial_height_coverage
end PrimitiveQuadraticMahler318
