module
public import ActualScalarRoot318
public section
noncomputable section
namespace ScalarForwardWitness318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open GeneratorScalarProgression318 (normCoefficient)
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def inputX (q : ℚ) : ℚ := q+q^2
@[expose] def inputFourth (q : ℚ) : ℚ :=
  (inputX q)^2+(496408687/100291113)*(inputX q)^3+(197130368/33430371)*(inputX q)^4
@[expose] def inputR (q : ℚ) : ℚ :=
  101783690143177584*inputX q+267108917866935984*(inputX q)^2+
    533801448346128768*inputFourth q+4376874610839020

lemma inputR_large (q : ℚ) (hq : 0≤q+q^2) : 10 < inputR q := by
  have hx : 0 ≤ inputX q := hq
  have hfour : 0 ≤ inputFourth q := by unfold inputFourth; positivity
  have hterm : 0≤101783690143177584*inputX q := by positivity
  have hterm2 : 0≤267108917866935984*(inputX q)^2 := by positivity
  have hterm3 : 0≤533801448346128768*inputFourth q := by positivity
  unfold inputR
  linarith

lemma integer_inputX (a : ℤ) : 0≤(a:ℚ)+(a:ℚ)^2 := by
  have hi : 0≤a*(a+1) := by
    by_cases ha : 0≤a
    · exact mul_nonneg ha (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hi' : 0≤(a:ℚ)*((a:ℚ)+1) := by exact_mod_cast hi
  nlinarith

lemma integer_inputR_large (a : ℤ) : 10 < inputR (a:ℚ) :=
  inputR_large _ (integer_inputX a)

@[expose] def N (w : Assignment) : ℚ := 1+(w 37/inputR (w 0))^2+2*w 33/inputR (w 0)
@[expose] def Q (w : Assignment) (n : ℤ) : ℚ :=
  ActualScalarRoot318.inverseNorm n/(w 37*(inputR (w 0))^15)
@[expose] def W (w : Assignment) (n : ℤ) : ℚ := (N w)^2+inputR (w 0)*(Q w n)^2
@[expose] def quotient (w : Assignment) (n : ℤ) : ℚ := W w n/(1+114444*inputR (w 0))
@[expose] def poleInput (w : Assignment) (n : ℤ) : ℚ :=
  114444*inputR (w 0)*(quotient w n)^2

@[expose] def fill (w : Assignment) (n : ℤ) : Assignment := fun i =>
  if i=296 then (inputX (w 0))^2 else
  if i=297 then inputFourth (w 0) else
  if i=298 then 1/inputR (w 0) else
  if i=299 then 1/(inputR (w 0))^2 else
  if i=300 then 1/(inputR (w 0))^4 else
  if i=301 then 1/(inputR (w 0))^8 else
  if i=302 then 1/(inputR (w 0))^16 else
  if i=303 then (ActualScalarRoot318.root n).re else
  if i=304 then (ActualScalarRoot318.root n).im else
  if i=305 then (pair (w 82) (w 83)*ActualScalarRoot318.root n).re else
  if i=306 then (pair (w 82) (w 83)*ActualScalarRoot318.root n).im else
  if i=307 then normCoefficient (ActualScalarRoot318.root n) else
  if i=308 then ActualScalarRoot318.inverseNorm n else
  if i=309 then w 37/inputR (w 0) else
  if i=310 then Q w n else
  if i=311 then N w-1 else
  if i=312 then (Q w n)^2 else
  if i=313 then quotient w n else
  if i=314 then poleInput w n else
  w i

/-- The19 scalar construction rows consume the same common norm and the
actual second labelled root. Only the pole certificate and final conic remain. -/
theorem scalar_rows (S : ℚ) (w : Assignment) (n : ℤ)
    (h0 : n≠0) (h1 : n≠1) (hq : w 118=(w 0)^2)
    (hroot : pair (w 82) (w 83)=CoherentMultipleCharts318.fixedRoot n)
    (hr : inputR (w 0)≠0) (hH : w 37≠0) (ha : 1+114444*inputR (w 0)≠0) :
    Constraints [r263 S,r264 S,r265 S,r266 S,r267 S,r268 S,r269 S,r270 S,r271 S,r272 S,r273 S,r274 S,r275 S,r276 S,r277 S,r278 S,r279 S,r280 S,r281 S] (fill w n) := by
  have hnR := ActualScalarRoot318.norm_ne n h0 h1
  simp only [Constraints,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · norm_num [r263,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      try dsimp [inputR,inputFourth,inputX] at hr ⊢
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r264,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      try dsimp [inputR,inputFourth,inputX] at hr ⊢
      field_simp [hr,hH,ha,hnR] <;> ring
  · have hrow : r265 S (fill w n) =
        -(1)+inputR (w 0)*(1/inputR (w 0)) := by
      norm_num [r265,fill,hq]
      unfold inputR inputFourth inputX
      ring
    rw [hrow]
    field_simp [hr] <;> ring
  · norm_num [r266,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r267,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r268,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r269,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r270,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r271,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · have he := ActualScalarRoot318.kummer n h0 h1
    rw [←hroot] at he
    have hh := congrArg QuadraticAlgebra.re he
    norm_num [CompressedOrientation318.k,CompressedOrientation318.m,CompressedOrientation318.D,
      pair,pow_succ] at hh
    norm_num [r272,fill,pair,pow_succ]
    linear_combination hh
  · have he := ActualScalarRoot318.kummer n h0 h1
    rw [←hroot] at he
    have hh := congrArg QuadraticAlgebra.im he
    norm_num [CompressedOrientation318.k,CompressedOrientation318.m,CompressedOrientation318.D,
      pair,pow_succ] at hh
    norm_num [r273,fill,pair,pow_succ]
    linear_combination hh
  · norm_num [r274,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r275,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      change -1+normCoefficient (ActualScalarRoot318.root n)*(normCoefficient (ActualScalarRoot318.root n))⁻¹=0
      rw [mul_inv_cancel₀ hnR]
      norm_num
  · have hrow : r276 S (fill w n) =
        -(w 37)+inputR (w 0)*(w 37/inputR (w 0)) := by
      norm_num [r276,fill,hq]
      unfold inputR inputFourth inputX
      ring
    rw [hrow]
    field_simp [hr] <;> ring
  · norm_num [r277,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r278,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · norm_num [r279,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring
  · have hquot : (1+114444*inputR (w 0))*quotient w n = W w n := by
      unfold quotient
      field_simp [ha] <;> ring
    have hrow : r280 S (fill w n) =
        -1-2*(N w-1)-(N w-1)^2-inputR (w 0)*(Q w n)^2+
          (1+114444*inputR (w 0))*quotient w n := by
      norm_num [r280,fill,hq]
      unfold inputR inputFourth inputX
      ring
    rw [hrow,hquot]
    unfold W
    ring
  · norm_num [r281,fill,pair,normCoefficient]
    all_goals
      try simp only [hq]
      try dsimp [poleInput,quotient,W,N,Q,ActualScalarRoot318.inverseNorm]
      field_simp [hr,hH,ha,hnR] <;> ring

lemma pole_squareclass (w : Assignment) (n : ℤ) :
    poleInput w n=(114444*inputR (w 0))*(quotient w n)^2 := by
  unfold poleInput
  ring

/-- The exact reduced scalar squareclass retains the original factor11. -/
lemma pole_squareclass_eleven (w : Assignment) (n : ℤ) :
    poleInput w n=(11*inputR (w 0))*(102*quotient w n)^2 := by
  unfold poleInput
  ring

end ScalarForwardWitness318
