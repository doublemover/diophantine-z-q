module
public import OriginalPolynomialExpansionBounds318
public section
noncomputable section
namespace OriginalReducedPolynomialExpansions318
open MvPolynomial LiteralSievePolynomial318 TernaryQuadraticLineCover318
open OriginalPolynomialExpansionBounds318 OriginalReducedPolynomialEquiv318
set_option maxHeartbeats 5000000

@[expose] def row (u v z : Vector ℚ) (i : Fin 3) : Expansion :=
  linearExpansion (if i=0 then (u.1,v.1,z.1) else if i=1 then (u.2.1,v.2.1,z.2.1)
    else (u.2.2,v.2.2,z.2.2))
@[expose] def square (e : Expansion) := mulExpansion e e
@[expose] def scaled (a : ℚ) (e : Expansion) := mulExpansion (constExpansion a) e
@[expose] def firstExpansion (κ t : ℚ) (x y w : Expansion) : Expansion :=
  addExpansion (scaled κ (square w)) (constExpansion (2*t))
@[expose] def secondExpansion (κ t : ℚ) (x y w : Expansion) : Expansion :=
  addExpansion (scaled (κ*(t+2)) (square w)) (scaled (-2) (mulExpansion x y))
@[expose] def productExpansion (t : ℚ) (x y : Expansion) : Expansion :=
  mulExpansion (addExpansion (constExpansion (t^2)) (square x))
    (addExpansion (constExpansion (t^2)) (square y))
@[expose] def coreExpansion (κ t : ℚ) (x y w : Expansion) : Expansion :=
  addExpansion (addExpansion (scaled κ (square w)) (scaled (-1) (mulExpansion x y)))
    (constExpansion (t^2+2*t))
@[expose] def normExpansion (κ t : ℚ) (x y w : Expansion) : Expansion :=
  addExpansion (square (coreExpansion κ t x y w)) (scaled (t^2) (square (addExpansion x y)))

lemma polynomial_row (u v z : Vector ℚ) (i : Fin 3) :
    polynomial (row u v z i)=variables u v z i := by
  fin_cases i <;> simp [row,variables,polynomial_linear]
lemma polynomial_square (e : Expansion) : polynomial (square e)=(polynomial e)^2 := by
  simp only [square,polynomial_mul,pow_two]
lemma polynomial_scaled (a : ℚ) (e : Expansion) : polynomial (scaled a e)=C a*polynomial e := by
  simp only [scaled,polynomial_mul,polynomial_const]
lemma weight_square (e : Expansion) : weight (square e)=(weight e)^2 := by
  simp only [square,weight_mul,pow_two]
lemma weight_scaled (a : ℚ) (e : Expansion) : weight (scaled a e)=|(a:ℝ)|*weight e := by
  simp only [scaled,weight_mul,weight_const]

/-- Exact symbolic expansions for all original reduced polynomials,
including multiplicity of repeated exponent vectors. -/
theorem original_expansions (κ t : ℚ) (u v z : Vector ℚ) :
    let x := row u v z 0
    let y := row u v z 1
    let w := row u v z 2
    polynomial (firstExpansion κ t x y w)=forward u v z (firstP κ t) ∧
    polynomial (secondExpansion κ t x y w)=forward u v z (secondP κ t) ∧
    polynomial (productExpansion t x y)=forward u v z (productD t) ∧
    polynomial (normExpansion κ t x y w)=forward u v z (normK κ t) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [firstExpansion,secondExpansion,productExpansion,normExpansion,coreExpansion,
    polynomial_add,polynomial_mul,polynomial_square,polynomial_scaled,polynomial_const,
    polynomial_row,firstP,secondP,productD,normK,forward,algebraMap_eq] <;> ring

/-- Explicit absolute coefficient masses before collection. -/
theorem original_weights (κ t : ℚ) (x y w : Expansion) :
    weight (firstExpansion κ t x y w)=|(κ:ℝ)|*(weight w)^2+2*|(t:ℝ)| ∧
    weight (secondExpansion κ t x y w)=|((κ*(t+2):ℚ):ℝ)|*(weight w)^2+2*weight x*weight y ∧
    weight (productExpansion t x y)=((t:ℝ)^2+(weight x)^2)*((t:ℝ)^2+(weight y)^2) ∧
    weight (normExpansion κ t x y w)=
      (|(κ:ℝ)|*(weight w)^2+weight x*weight y+|(t:ℝ)^2+2*(t:ℝ)|)^2+
        (t:ℝ)^2*(weight x+weight y)^2 := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [firstExpansion,secondExpansion,productExpansion,normExpansion,coreExpansion,
    weight_add,weight_mul,weight_square,weight_scaled,weight_const,
    Rat.cast_mul,Rat.cast_add,Rat.cast_pow,abs_mul,abs_sq] <;> ring

end OriginalReducedPolynomialExpansions318
