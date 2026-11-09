module
public import NormalizedGeneratorIndependence318
public import ActualQuadraticEmbeddings318
public section
noncomputable section

/-! One actual real embedding of the whole radical field, choosing both
positive roots and recovering the original two real embeddings of K. -/
namespace NormalizationRealEmbedding318
open ConcreteG8Domain (K)
open NormalizingRadicals318 NormalizedPointSigns318 NormalizationInjection318
open NormalizedGeneratorIndependence318 ActualQuadraticEmbeddings318
open ReciprocalDouble318 ShortCurveBaseChange318
open WeierstrassCurve.Affine
local instance : DecidableEq Both := Classical.decEq Both
local instance : DecidableEq ℝ := Classical.decEq ℝ
set_option maxHeartbeats 1000000

/-- Evaluate the literal quadratic algebra through the specified base map. -/
@[expose] def extendRoot {F : Type*} [Field F] (φ : F →+* ℝ)
    (d : F) (r : ℝ) (hr : r^2=φ d) : QuadraticAlgebra F d 0 →+* ℝ := by
  letI : Algebra F ℝ := φ.toAlgebra
  exact (QuadraticAlgebra.lift (a:=d) (b:=(0:F)) ⟨r,by
    simpa [Algebra.smul_def,pow_two] using hr⟩).toRingHom

lemma extendRoot_apply {F : Type*} [Field F] (φ : F →+* ℝ)
    (d : F) (r : ℝ) (hr : r^2=φ d) (z : QuadraticAlgebra F d 0) :
    extendRoot φ d r hr z=φ z.re+φ z.im*r := by
  simp [extendRoot,QuadraticAlgebra.lift_apply_apply,Algebra.smul_def]

lemma extendRoot_base {F : Type*} [Field F] (φ : F →+* ℝ)
    (d : F) (r : ℝ) (hr : r^2=φ d) (x : F) :
    extendRoot φ d r hr (algebraMap F (QuadraticAlgebra F d 0) x)=φ x := by
  simp [extendRoot_apply]

lemma positive_delta : 0<positiveEmbedding delta := by
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hb : Real.sqrt (2:ℝ)<2 := by nlinarith
  simpa [delta,positiveEmbedding,realEmbedding_pair] using (show 0<3-Real.sqrt (2:ℝ) by linarith)

lemma positive_deltaBar : 0<positiveEmbedding deltaBar := by
  have hs := Real.sqrt_nonneg (2:ℝ)
  simpa [deltaBar,positiveEmbedding,realEmbedding_pair] using (show 0<3+Real.sqrt (2:ℝ) by linarith)

@[expose] def alpha : ℝ := Real.sqrt (positiveEmbedding delta)
@[expose] def beta : ℝ := Real.sqrt (positiveEmbedding deltaBar)

lemma alpha_pos : 0<alpha := Real.sqrt_pos.mpr positive_delta
lemma beta_pos : 0<beta := Real.sqrt_pos.mpr positive_deltaBar
lemma alpha_square : alpha^2=positiveEmbedding delta := Real.sq_sqrt positive_delta.le
lemma beta_square : beta^2=positiveEmbedding deltaBar := Real.sq_sqrt positive_deltaBar.le

@[expose] def firstEmbedding : First →+* ℝ :=
  extendRoot positiveEmbedding delta alpha alpha_square

lemma firstEmbedding_base (x : K) :
    firstEmbedding (algebraMap K First x)=positiveEmbedding x :=
  extendRoot_base _ _ _ _ x

@[expose] def realEmbedding : Both →+* ℝ :=
  extendRoot firstEmbedding (algebraMap K First deltaBar) beta
    (beta_square.trans (firstEmbedding_base deltaBar).symm)

lemma realEmbedding_first (x : First) :
    realEmbedding (algebraMap First Both x)=firstEmbedding x :=
  extendRoot_base _ _ _ _ x

lemma realEmbedding_base (x : K) : realEmbedding (base x)=positiveEmbedding x := by
  change realEmbedding (algebraMap First Both (algebraMap K First x))=positiveEmbedding x
  rw [realEmbedding_first,firstEmbedding_base]

lemma realEmbedding_firstRoot : realEmbedding firstRoot=alpha := by
  rw [firstRoot,realEmbedding_first]
  simp [firstEmbedding,extendRoot_apply]

lemma realEmbedding_secondRoot : realEmbedding secondRoot=beta := by
  simp [realEmbedding,secondRoot,extendRoot_apply]

lemma realEmbedding_conjugateBase (x : K) :
    realEmbedding (conjugateBase x)=negativeEmbedding x := by
  change realEmbedding (base (SourceContact318.conj x))=negativeEmbedding x
  rw [realEmbedding_base]
  rcases x with ⟨a,b⟩
  change positiveEmbedding (SourceContact318.conj (ConcreteG8Domain.pair a b))=
    negativeEmbedding (ConcreteG8Domain.pair a b)
  simp [positiveEmbedding,negativeEmbedding,realEmbedding_pair]

/-- Injective real base change on the same coefficient-one elliptic curve. -/
@[expose] def realPoint : (E (1:Both)).Point →+ (E (1:ℝ)).Point :=
  (transport (congrArg E realEmbedding.map_one)).toAddMonoidHom.comp
    (pointMap realEmbedding 1)

lemma realPoint_injective : Function.Injective realPoint :=
  (transport (congrArg E realEmbedding.map_one)).injective.comp
    (pointMap_injective realEmbedding 1)

@[expose] def firstRealGenerator : (E (1:ℝ)).Point := realPoint firstGenerator
@[expose] def secondRealGenerator : (E (1:ℝ)).Point := realPoint secondGenerator

/-- Integer independence now holds for actual real elliptic points, with
the chosen root signs and both original real embeddings proved above. -/
theorem real_integer_relation (m n : ℤ)
    (h : m • firstRealGenerator+n • secondRealGenerator=0) : m=0 ∧ n=0 := by
  apply integer_relation m n
  apply realPoint_injective
  simpa only [map_add,map_zsmul,map_zero] using h

lemma realPoint_some (x y : Both) (h : (E (1:Both)).Nonsingular x y) :
    ∃ h' : (E (1:ℝ)).Nonsingular (realEmbedding x) (realEmbedding y),
      realPoint (Point.some x y h)=Point.some _ _ h' := by
  change ∃ h', transport (congrArg E realEmbedding.map_one)
    (pointMap realEmbedding 1 (Point.some x y h))=Point.some _ _ h'
  rw [pointMap_some,transport_some]
  exact ⟨_,rfl⟩

lemma firstRealGenerator_coordinates :
    ∃ h : (E (1:ℝ)).Nonsingular (alpha⁻¹^2*positiveEmbedding LocalGenerator318.xP)
        (alpha⁻¹^3*positiveEmbedding LocalGenerator318.yP),
      firstRealGenerator=Point.some _ _ h := by
  obtain ⟨h,he⟩ := normalize_some base ConcreteG8Domain.D firstRoot firstRoot_ne first_coefficient
    LocalGenerator318.xP LocalGenerator318.yP LocalGenerator318.nonsingularP
  change ∃ h', realPoint (normalize base ConcreteG8Domain.D firstRoot firstRoot_ne first_coefficient
    (Point.some _ _ _))=Point.some _ _ h'
  rw [he]
  have hm := realPoint_some _ _ h
  simpa only [map_mul,map_pow,map_inv₀,realEmbedding_firstRoot,realEmbedding_base] using hm

lemma secondRealGenerator_coordinates :
    ∃ h : (E (1:ℝ)).Nonsingular (beta⁻¹^2*negativeEmbedding LocalGenerator318.xP)
        (beta⁻¹^3*negativeEmbedding LocalGenerator318.yP),
      secondRealGenerator=Point.some _ _ h := by
  obtain ⟨h,he⟩ := normalize_some conjugateBase ConcreteG8Domain.D secondRoot secondRoot_ne conjugate_coefficient
    LocalGenerator318.xP LocalGenerator318.yP LocalGenerator318.nonsingularP
  change ∃ h', realPoint (normalize conjugateBase ConcreteG8Domain.D secondRoot secondRoot_ne conjugate_coefficient
    (Point.some _ _ _))=Point.some _ _ h'
  rw [he]
  have hm := realPoint_some _ _ h
  simpa only [map_mul,map_pow,map_inv₀,realEmbedding_secondRoot,realEmbedding_conjugateBase] using hm

end NormalizationRealEmbedding318
