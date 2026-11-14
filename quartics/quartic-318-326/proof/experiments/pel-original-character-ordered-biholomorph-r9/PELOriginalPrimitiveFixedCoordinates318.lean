module
public import PELOriginalFixedPolygonSearch318
public import PELNontrivialFixedTraceZero318
public import PELPositiveEllipticLabels318
public section
noncomputable section
namespace PELOriginalPrimitiveFixedCoordinates318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELLevelThreeSimilitudes318 PELIntegralEllipticObstructions318 PELActualOrderNormalizer318
open PELNormalizerPrimitiveRepresentative318 PELQuaternionNormParity318 QuaternionicFixedParameter318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELOriginalFixedIntegralCoordinates318
set_option maxHeartbeats 2400000

/-- Removing a nonzero scalar from the ACTUAL matrix preserves the same
fixed complex line. This is not a claim about an abstract fixed-point table. -/
theorem fixesLine_smul_iff (q : ℝ) (hq : q≠0) (M : RealMatrices) (τ : ℂ) :
    fixesLine (q • M) τ ↔ fixesLine M τ := by
  have hqC : (q:ℂ)≠0 := by exact_mod_cast hq
  unfold fixesLine
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  constructor
  · intro h
    apply mul_left_cancel₀ hqC
    linear_combination h
  · intro h
    linear_combination (q:ℂ)*h

/-- Primitive coordinates are obtained from the original rational
normalizer at the SAME fixed upper-half-plane point. Their trace and norm
are constructed, not supplied by the caller. -/
theorem primitive_fixed (u : positiveNormalizer) (τ : HalfPlane)
    (hfix : baseAction u τ=τ) (ht : reducedTrace (u.val:B)=0) :
    ∃ (a : Coordinates) (i : Fin 5), trace a=0 ∧
      integralNorm a=(PELFixedNormalizerFiniteSearch318.norm i:ℤ) ∧
      fixesLine (representation (embed a)) τ := by
  let U : normalizer := ⟨u.val,u.property.1⟩
  obtain ⟨q,a,z,w,hu,ha,hprimitive,hdiv,hnorm⟩ := primitive_representative U
  have hq : 0<(q:ℚ)^2 := sq_pos_of_ne_zero q.ne_zero
  have hNQ : 0<(integralNorm a:ℚ) := by
    have hh : 0<(q:ℚ)^2*(integralNorm a:ℚ) := by rw [←hnorm]; exact u.property.2
    exact pos_of_mul_pos_left hh hq.le
  have hN : 0<integralNorm a := by exact_mod_cast hNQ
  have htrace : reducedTrace (u.val:B)=(q:ℚ)*(trace a:ℚ) := by
    change reducedTrace (U.val:B)=_
    rw [hu]
    change reducedTrace (algebraMap ℚ B (q:ℚ)*(w.val:B))=_
    rw [PELPositiveEllipticLabels318.trace_scalar_mul,←ha,original_trace]
  have hta : trace a=0 := by
    have hz : (q:ℚ)*(trace a:ℚ)=0 := htrace.symm.trans ht
    exact_mod_cast (mul_eq_zero.mp hz).resolve_left q.ne_zero
  obtain ⟨_,i,hi⟩ := PELPrimitiveEllipticNorms318.classification w a ha hN hdiv
    (by rw [hta]; nlinarith)
  have hi' : integralNorm a=(PELFixedNormalizerFiniteSearch318.norm i:ℤ) := by
    rw [hi]
    fin_cases i <;> norm_num [PELInertiaNormalizerData318.discriminant,
      PELFixedNormalizerFiniteSearch318.norm]
  have hf : fixesLine (representation (u.val:B)) τ :=
    fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive u) τ τ.property)
      (congrArg Subtype.val hfix)
  have hm : representation (u.val:B)=((q:ℚ):ℝ) • representation (embed a) := by
    change representation (U.val:B)=_
    rw [hu]
    change representation (algebraMap ℚ B (q:ℚ)*(w.val:B))=_
    rw [←ha]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [representation,PELQuaternionRealRepresentation318.matrix,
        QuaternionAlgebra.algebraMap_eq,Matrix.smul_apply] <;> push_cast <;> ring
  rw [hm] at hf
  have hqR : ((q:ℚ):ℝ)≠0 := by exact_mod_cast q.ne_zero
  exact ⟨a,i,hta,hi',(fixesLine_smul_iff _ hqR _ _).mp hf⟩

/-- Overall sign is removed using the original scalar -1; all remaining
independent coordinate signs are retained for the complete finite list. -/
theorem positive_rotation (a : Coordinates) (ht : trace a=0)
    (hn : 0<integralNorm a) (τ : HalfPlane)
    (hf : fixesLine (representation (embed a)) τ) :
    ∃ b : Coordinates, trace b=0 ∧ integralNorm b=integralNorm a ∧
      0<rotationCoordinate b ∧ fixesLine (representation (embed b)) τ := by
  have he := norm_equation a ht
  have hr : rotationCoordinate a≠0 := by
    intro hz; rw [hz] at he; nlinarith [sq_nonneg (a 0),sq_nonneg (a 3)]
  by_cases hp : 0<rotationCoordinate a
  · exact ⟨a,ht,rfl,hp,hf⟩
  · refine ⟨-a,?_,?_,?_,?_⟩
    · change 2*(-a 0)+(-a 2)=0
      unfold trace at ht
      omega
    · simp [integralNorm]; ring
    · change 0<2*(-a 1)+(-a 3)
      unfold rotationCoordinate at hp hr
      omega
    · rw [embed_neg,map_neg]
      have hh : fixesLine ((-1:ℝ) • representation (embed a)) τ :=
        (fixesLine_smul_iff (-1) (by norm_num) _ _).mpr hf
      simpa only [neg_one_smul] using hh

/-- Every original trace-zero fixed normalizer admits the exact positive-r
integral source required by the finite search. -/
theorem positive_primitive_fixed (u : positiveNormalizer) (τ : HalfPlane)
    (hf : baseAction u τ=τ) (ht : reducedTrace (u.val:B)=0) :
    ∃ (a : Coordinates) (i : Fin 5), trace a=0 ∧
      integralNorm a=(PELFixedNormalizerFiniteSearch318.norm i:ℤ) ∧
      0<rotationCoordinate a ∧ fixesLine (representation (embed a)) τ := by
  obtain ⟨a,i,ha,hi,hfix⟩ := primitive_fixed u τ hf ht
  have hn : 0<integralNorm a := by
    rw [hi]; fin_cases i <;> norm_num [PELFixedNormalizerFiniteSearch318.norm]
  obtain ⟨b,hb,hbn,hbr,hbf⟩ := positive_rotation a ha hn τ hfix
  exact ⟨b,i,hb,hbn.trans hi,hbr,hbf⟩
end PELOriginalPrimitiveFixedCoordinates318
