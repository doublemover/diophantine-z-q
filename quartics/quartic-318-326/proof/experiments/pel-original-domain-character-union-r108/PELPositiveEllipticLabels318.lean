module
public import PELPrimitiveEllipticNorms318
public section
noncomputable section
namespace PELPositiveEllipticLabels318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELLevelThreeSimilitudes318
open PELIntegralEllipticObstructions318 PELActualOrderNormalizer318
open PELNormalizerPrimitiveRepresentative318 PELQuaternionNormParity318
set_option maxHeartbeats 1800000

theorem trace_scalar_mul (q : ℚ) (x : B) :
    reducedTrace (algebraMap ℚ B q*x)=q*reducedTrace x := by
  simp [reducedTrace,QuaternionAlgebra.algebraMap_eq] <;> ring

/-- Every actual positive rational normalizer with STRICT elliptic trace
bound has one of the five ORIGINAL inertia parity labels. This classifies
possible labels, not conjugacy classes or complete geometric branch orbits. -/
theorem original_five_labels (u : PELPositiveOrderNormalizer318.positiveNormalizer)
    (hbound : reducedTrace (u.val:B)^2<4*reducedNorm (u.val:B)) :
    ∃ i : Fin 5,PELPositiveOrderNormalizer318.parity u=
      Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) := by
  let U : normalizer := ⟨u.val,u.property.1⟩
  obtain ⟨q,a,z,w,hu,ha,hprimitive,hdiv,hnorm⟩ := primitive_representative U
  have htrace : reducedTrace (u.val:B)=(q:ℚ)*(trace a:ℚ) := by
    change reducedTrace (U.val:B)=_
    rw [hu]
    change reducedTrace (algebraMap ℚ B (q:ℚ)*(w.val:B))=_
    rw [trace_scalar_mul,←ha,original_trace]
  have hq : 0<(q:ℚ)^2 := sq_pos_of_ne_zero q.ne_zero
  have hNQ : 0<(integralNorm a:ℚ) := by
    have hh : 0<(q:ℚ)^2*(integralNorm a:ℚ) := by
      rw [←hnorm]
      exact u.property.2
    exact pos_of_mul_pos_left hh hq.le
  have hN : 0<integralNorm a := by exact_mod_cast hNQ
  have hs : (q:ℚ)^2*(trace a:ℚ)^2<(q:ℚ)^2*(4*(integralNorm a:ℚ)) := by
    change reducedTrace (U.val:B)^2<4*reducedNorm (U.val:B) at hbound
    rw [hnorm] at hbound
    change reducedTrace (u.val:B)^2<_ at hbound
    rw [htrace] at hbound
    nlinarith only [hbound]
  have hbQ : (trace a:ℚ)^2<4*(integralNorm a:ℚ) := (mul_lt_mul_left hq).mp hs
  have hb : trace a^2<4*integralNorm a := by exact_mod_cast hbQ
  obtain ⟨ht,i,hi⟩ := PELPrimitiveEllipticNorms318.classification w a ha hN hdiv hb
  have hw : reducedNorm (w.val:B)=
      reducedNorm (PELInertiaPrimeWord318.word (InertiaLabels318.fiveLabels i):B) := by
    rw [←ha,original_norm,PELInertiaPrimeWord318.original_word_norm,hi] <;> norm_num
  have hp : parity w.val=InertiaLabels318.fiveLabels i := by
    rw [←parity_word (InertiaLabels318.fiveLabels i)]
    funext j
    change (padicValRat (PELPrimeNormalizerData318.prime j) (reducedNorm (w.val:B)):ZMod 2)=_
    rw [hw]
  refine ⟨i,?_⟩
  change parity U.val=InertiaLabels318.fiveLabels i
  rw [hu,parity_mul,parity_scalar,zero_add,hp]
end PELPositiveEllipticLabels318
