module
public import ConcreteG8Domain
public import SquareReflection318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section

/-! Concrete independent normalizing radicals for the two real quartics.
This constructs an actual quadratic tower and its selective sign involution;
it does not assert an elliptic logarithm or real-density comparison. -/
namespace NormalizingRadicals318
open ConcreteG8Domain (K pair)
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

@[expose] def delta : K := pair 3 (-1)
@[expose] def deltaBar : K := pair 3 1

lemma delta_square : delta^2=ConcreteG8Domain.D := by
  ext <;> norm_num [delta,ConcreteG8Domain.D,ConcreteG8Domain.i,pair,pow_succ]

lemma delta_product : delta*deltaBar=(7:K) := by
  ext <;> norm_num [delta,deltaBar,pair]

lemma norm_delta : QuadraticAlgebra.norm delta=(7:ℚ) := by
  norm_num [delta,pair,QuadraticAlgebra.norm_def]

lemma norm_deltaBar : QuadraticAlgebra.norm deltaBar=(7:ℚ) := by
  norm_num [deltaBar,pair,QuadraticAlgebra.norm_def]

lemma rat_seven_not_square : ¬IsSquare (7:ℚ) := by
  intro hs
  have hi : IsSquare (7:ℤ) :=
    (SquareReflection318.fraction_square_iff (R:=ℤ) (K:=ℚ) 7).mp (by simpa using hs)
  obtain ⟨z,hz⟩ := hi
  have hlo : -3<z := by nlinarith [sq_nonneg (z+3)]
  have hhi : z<3 := by nlinarith [sq_nonneg (z-3)]
  interval_cases z <;> norm_num at hz

lemma rat_fourteen_not_square : ¬IsSquare (14:ℚ) := by
  intro hs
  have hi : IsSquare (14:ℤ) :=
    (SquareReflection318.fraction_square_iff (R:=ℤ) (K:=ℚ) 14).mp (by simpa using hs)
  obtain ⟨z,hz⟩ := hi
  have hlo : -4<z := by nlinarith [sq_nonneg (z+4)]
  have hhi : z<4 := by nlinarith [sq_nonneg (z-4)]
  interval_cases z <;> norm_num at hz

lemma seven_not_square : ¬IsSquare (7:K) := by
  intro hs
  have hs' : IsSquare (algebraMap ℚ K (7:ℚ)) := by simpa using hs
  rcases (SquareReflection318.quadratic_square_iff (2:ℚ) 7 (by norm_num)).mp hs' with h|h
  · exact rat_seven_not_square h
  · apply rat_fourteen_not_square
    simpa only [show (2:ℚ)*7=14 by norm_num] using h

lemma delta_not_square : ¬IsSquare delta := by
  rintro ⟨x,hx⟩
  apply rat_seven_not_square
  refine ⟨QuadraticAlgebra.norm x,?_⟩
  have he := congrArg (fun y : K => QuadraticAlgebra.norm y) hx
  simpa only [norm_delta,map_mul] using he

lemma deltaBar_not_square : ¬IsSquare deltaBar := by
  rintro ⟨x,hx⟩
  apply rat_seven_not_square
  refine ⟨QuadraticAlgebra.norm x,?_⟩
  have he := congrArg (fun y : K => QuadraticAlgebra.norm y) hx
  simpa only [norm_deltaBar,map_mul] using he

lemma delta_ne_zero : delta≠0 := by
  intro hz
  have he := congrArg QuadraticAlgebra.re hz
  norm_num [delta,pair] at he

/-- First actual normalization field K(sqrt(3-sqrt(2))). -/
abbrev First := QuadraticAlgebra K delta 0

instance firstField : Field First := by
  letI : Fact (¬IsSquare delta) := ⟨delta_not_square⟩
  infer_instance

/-- The other normalizing radical is still nonsquare after the first extension.
The only possible square-class alternatives are deltaBar and delta*deltaBar=7. -/
lemma second_not_square : ¬IsSquare (algebraMap K First deltaBar) := by
  intro hs
  rcases (SquareReflection318.quadratic_square_iff delta deltaBar delta_ne_zero).mp hs with h|h
  · exact deltaBar_not_square h
  · exact seven_not_square (by simpa only [delta_product] using h)

/-- Both independent normalizing radicals in one actual field. -/
abbrev Both := QuadraticAlgebra First (algebraMap K First deltaBar) 0

instance bothField : Field Both := by
  letI : Fact (¬IsSquare (algebraMap K First deltaBar)) := ⟨second_not_square⟩
  infer_instance

lemma degree_four : Module.finrank K Both=4 := by
  rw [←Module.finrank_mul_finrank K First Both,QuadraticAlgebra.finrank_eq_two,
    QuadraticAlgebra.finrank_eq_two]

@[expose] def firstRoot : Both := algebraMap First Both (⟨0,1⟩ : First)
@[expose] def secondRoot : Both := ⟨0,1⟩

lemma firstRoot_square : firstRoot^2=algebraMap First Both (algebraMap K First delta) := by
  rw [firstRoot,←map_pow]
  congr 1
  ext <;> simp [pow_two]

lemma secondRoot_square : secondRoot^2=algebraMap First Both (algebraMap K First deltaBar) := by
  ext <;> simp [secondRoot,pow_two]

/-- Selective conjugation fixes the first normalization field pointwise and
negates the second radical. It is an actual algebra automorphism, not a chosen
sign on a real numerical approximation. -/
@[expose] def flipSecond : Both≃ₐ[First]Both where
  toFun z := ⟨z.re,-z.im⟩
  invFun z := ⟨z.re,-z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring
  commutes' x := by ext <;> simp

lemma flipSecond_firstRoot : flipSecond firstRoot=firstRoot :=
  flipSecond.commutes _

lemma flipSecond_secondRoot : flipSecond secondRoot= -secondRoot := by
  ext <;> simp [flipSecond,secondRoot]

lemma flipSecond_base (x : K) :
    flipSecond (algebraMap First Both (algebraMap K First x))=
      algebraMap First Both (algebraMap K First x) := flipSecond.commutes _

end NormalizingRadicals318
