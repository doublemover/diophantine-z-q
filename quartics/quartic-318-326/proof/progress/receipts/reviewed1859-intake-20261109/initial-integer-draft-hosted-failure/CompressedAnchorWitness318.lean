module
public import CompressedPoint318
public import ActualQuadraticEmbeddings318
public section

/-! Forward witnesses for the literal compressed-anchor block. This is a
construction from a nonzero reciprocal elliptic chart, not an assumption
that the compressed rows have a solution. No other source block is claimed. -/
namespace CompressedAnchorWitness318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay CompressedOrientation318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

/-- The denominator used in the actual forward compression is everywhere
nonzero over the actual real quadratic field. -/
theorem denominator_nonzero (u : K) : k^2+D*u^2≠0 := by
  let σ := ActualQuadraticEmbeddings318.positiveEmbedding
  have hk : σ k≠0 := by
    intro h
    apply CompressedPoint318.k_ne
    exact σ.injective (by simpa using h)
  have hD : D=(3-ConcreteG8Domain.i)^2 := by
    ext <;> norm_num [D,ConcreteG8Domain.i,pair,pow_two]
  have hp : 0<(σ k)^2 := sq_pos_of_ne_zero hk
  have hn : 0≤σ D*(σ u)^2 := by
    rw [hD,map_pow]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  intro h
  have hz := congrArg σ h
  simp only [map_add,map_pow,map_mul,map_zero] at hz
  nlinarith

/-- The actual forward parameter, including its original orientation. -/
@[expose] def shiftWitness (u v : K) : K :=
  (k*v/u-m)/(k^2+D*u^2)

theorem ordinate_identity (u v : K) :
    m+(k^2+D*u^2)*shiftWitness u v=k*v/u := by
  dsimp only [shiftWitness]
  field_simp [denominator_nonzero u]
  ring

/-- Recover the compression equation from the original reciprocal chart.
Only u≠0 is required: v=0 and shiftWitness=0 are not discarded. -/
theorem compression_equation (u v : K) (hu : u≠0)
    (hc : v^2=1-D*u^4) :
    1=k^2*(u^2+u^2*(shiftWitness u v)^2)+
      2*m*(u^2*shiftWitness u v)+D*(u^2*shiftWitness u v)^2 := by
  let s := shiftWitness u v
  have ho : m+(k^2+D*u^2)*s=k*v/u := ordinate_identity u v
  have ha : u^2*(m+(k^2+D*u^2)*s)^2=k^2*(1-D*(u^2)^2) := by
    rw [ho]
    calc
      u^2*(k*v/u)^2 = k^2*v^2 := by field_simp [hu]; ring
      _ = k^2*(1-D*(u^2)^2) := by rw [hc]; ring
  have hf : (k^2+D*u^2)*
      (1-(k^2*(u^2+u^2*s^2)+2*m*(u^2*s)+D*(u^2*s)^2))=0 := by
    linear_combination u^2*CompressedPoint318.constant_equation - ha
  have hz := (mul_eq_zero.mp hf).resolve_left (denominator_nonzero u)
  exact (sub_eq_zero.mp hz)

/-- The square root of the rational norm is constructed, not supplied. -/
theorem norm_square (u : K) :
    (u.re^2-2*u.im^2)^2=(u^2).re^2-2*(u^2).im^2 := by
  rcases u with ⟨a,b⟩
  norm_num [pow_two]
  ring

/-- Fill precisely the nine stored coordinates of the seven-row block. -/
@[expose] def fill (base : Assignment) (u v : K) : Assignment :=
  fun i =>
    if i=33 then (u^2).re else
    if i=34 then (u^2).im else
    if i=35 then (shiftWitness u v).re else
    if i=36 then (shiftWitness u v).im else
    if i=37 then u.re^2-2*u.im^2 else
    if i=74 then (u^2*shiftWitness u v).re else
    if i=75 then (u^2*shiftWitness u v).im else
    if i=76 then (u^2*(shiftWitness u v)^2).re else
    if i=77 then (u^2*(shiftWitness u v)^2).im else base i

@[simp] theorem fill_input (base : Assignment) (u v : K) :
    fill base u v 0=base 0 := by simp [fill]

theorem fill_other (base : Assignment) (u v : K) (i : ℕ)
    (hi : i∉([33,34,35,36,37,74,75,76,77] : List ℕ)) :
    fill base u v i=base i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  simp_all [fill]

@[simp] theorem filled_fH (base : Assignment) (u v : K) :
    fH (fill base u v)=u^2 := by
  ext <;> simp [fH,fill,pair]

@[simp] theorem filled_shift (base : Assignment) (u v : K) :
    shift (fill base u v)=shiftWitness u v := by
  ext <;> simp [shift,fill,pair]

@[simp] theorem filled_mid (base : Assignment) (u v : K) :
    mid (fill base u v)=u^2*shiftWitness u v := by
  ext <;> simp [mid,fill,pair]

@[simp] theorem filled_fV (base : Assignment) (u v : K) :
    fV (fill base u v)=u^2*(shiftWitness u v)^2 := by
  ext <;> simp [fV,fill,pair]

/-- All seven original raw rows hold for the constructed assignment, with
no modified residual and no omitted gate. -/
theorem literal_rows (S : ℚ) (base : Assignment) (u v : K)
    (hu : u≠0) (hc : v^2=1-D*u^4) :
    r32 S (fill base u v)=0 ∧ r33 S (fill base u v)=0 ∧
    r34 S (fill base u v)=0 ∧ r35 S (fill base u v)=0 ∧
    r36 S (fill base u v)=0 ∧ r37 S (fill base u v)=0 ∧
    r38 S (fill base u v)=0 := by
  have he := compression_equation u v hu hc
  have hre := congrArg QuadraticAlgebra.re he
  have him := congrArg QuadraticAlgebra.im he
  have hn := norm_square u
  have hm : u^2*(shiftWitness u v)^2=(u^2*shiftWitness u v)*shiftWitness u v := by ring
  constructor
  · simp [r32,fill,pow_two]; ring
  constructor
  · simp [r33,fill,pow_two]; ring
  constructor
  · simp [r34,fill,hm,pow_two]; ring
  constructor
  · simp [r35,fill,hm,pow_two]; ring
  constructor
  · norm_num [k,m,D,pair,pow_two] at hre
    norm_num [r36,fill,pow_two] 
    linear_combination hre
  constructor
  · norm_num [k,m,D,pair,pow_two] at him
    norm_num [r37,fill,pow_two]
    linear_combination him
  · norm_num only [r38,fill]
    linear_combination hn

/-- The compressed reconstruction is the original chosen elliptic point,
not merely some point satisfying the same curve equation. -/
theorem reconstruct_original (base : Assignment) (u v : K) (hu : u≠0) :
    CompressedPoint318.xH (fill base u v)=1/u^2 ∧
    CompressedPoint318.yH (fill base u v)=v/u^3 := by
  constructor
  · simp [CompressedPoint318.xH]
  · have ha : RawLucasOrientation318.anchorA (fill base u v)=k*v/u := by
      simp only [RawLucasOrientation318.anchorA,filled_shift,filled_mid]
      have h := ordinate_identity u v
      linear_combination h
    rw [CompressedPoint318.yH,ha,filled_fH]
    field_simp [hu,CompressedPoint318.k_ne]
    ring

#print axioms literal_rows
#print axioms reconstruct_original
end CompressedAnchorWitness318
