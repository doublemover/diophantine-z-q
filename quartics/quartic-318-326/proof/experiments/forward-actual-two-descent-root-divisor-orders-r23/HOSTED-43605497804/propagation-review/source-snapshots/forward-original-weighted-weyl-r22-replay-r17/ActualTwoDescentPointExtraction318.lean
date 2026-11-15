module
public import ActualTwoDescentDiagonalExtension318
public section
noncomputable section
namespace ActualTwoDescentPointExtraction318
open TwoTwistPointRealization318
set_option maxHeartbeats 16000000

/-- Actual rational Kummer coordinates for the original curve
Y²=X(X-n)(X+3n), in the retained descent convention (X+3n,X-n).
This records a rational point, NOT an adelic/local solution or Selmer class.
Existence of this rational data is still the global arithmetic obligation. -/
structure KummerPoint (β n : ℚ) where
  x : ℚ
  y : ℚ
  u : ℚ
  v : ℚ
  x_ne : x ≠ 0
  u_ne : u ≠ 0
  v_ne : v ≠ 0
  curve : y^2=x*(x-n)*(x+3*n)
  first : x+3*n=β*u^2
  second : x-n=v^2

/-- The original x-coordinate has class beta because the TWO actual
Kummer coordinates multiply to beta times a square. This supplies the exact
nonzero root required by the existing simultaneous-point converter. -/
def KummerPoint.squareclass {β n : ℚ} (hβ : β ≠ 0) (P : KummerPoint β n) :
    SquareclassPoint β n := by
  have hy : P.y ≠ 0 := by
    intro hz
    have he := P.curve
    rw [P.first,P.second,hz,zero_pow (by omega : (2:ℕ) ≠ 0)] at he
    exact (mul_ne_zero (mul_ne_zero P.x_ne (pow_ne_zero 2 P.v_ne))
      (mul_ne_zero hβ (pow_ne_zero 2 P.u_ne))) he.symm
  let r : ℚ := P.y/(β*P.u*P.v)
  have hr : r ≠ 0 := div_ne_zero hy (mul_ne_zero (mul_ne_zero hβ P.u_ne) P.v_ne)
  have hx : β*r^2=P.x := by
    dsimp [r]
    rw [div_pow,P.curve,P.first,P.second]
    field_simp [hβ,P.u_ne,P.v_ne] <;> ring
  refine ⟨r,P.y,hr,?_⟩
  rw [hx]
  exact P.curve

/-- Once the two retained Kummer classes are represented by actual
rational points, their common n and the literal squareclass maps construct
the exact Realization at b. No unrelated curve, twist or source index enters. -/
def actual_realization_of_kummer (b β θ c d n : ℚ)
    (hβ : β ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hB : 17*b=β*c^2) (hV : (17*b)^2*(1-b/17)=θ*d^2)
    (P : KummerPoint β n) (Q : KummerPoint β (n*θ)) : Realization b where
  β := β
  θ := θ
  c := c
  d := d
  n := n
  c_ne := hc
  d_ne := hd
  first_class := hB
  second_class := hV
  first := P.squareclass hβ
  second := Q.squareclass hβ

/-- Four rational realizations can be extracted independently AFTER
their four poles have been fixed at one source index. This theorem does not
choose a new source index or infer point existence from local solvability. -/
def actual_four_realizations (b β θ c d n : Fin 4 → ℚ)
    (hβ : ∀ i, β i ≠ 0) (hc : ∀ i, c i ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hB : ∀ i, 17*b i=β i*(c i)^2)
    (hV : ∀ i, (17*b i)^2*(1-b i/17)=θ i*(d i)^2)
    (P : ∀ i, KummerPoint (β i) (n i))
    (Q : ∀ i, KummerPoint (β i) (n i*θ i)) : ∀ i, Realization (b i) :=
  fun i => actual_realization_of_kummer (b i) (β i) (θ i) (c i) (d i) (n i)
    (hβ i) (hc i) (hd i) (hB i) (hV i) (P i) (Q i)

end ActualTwoDescentPointExtraction318
