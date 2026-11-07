module
public import OrientedSourceLabels318
public section
namespace GlobalLogRatios318
open ConcreteG8Domain CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- The finite V branch cannot be either permitted pure torsion offset. -/
theorem source_V_not_pure_torsion (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hs:CompressedOrientation318.shift w≠0) :
    transport curve_eq (CompressedTranslation318.V S w source)≠0 ∧
      transport curve_eq (CompressedTranslation318.V S w source)≠T 0 := by
  rw [CompressedTranslation318.V,dite_eq_right hs,transport_some]
  constructor
  · exact Point.some_ne_zero _
  · intro he
    rw [T,Point.some.injEq] at he
    exact (CompressedGlobal318.source_global_V S w source hs).1 he.2

theorem source_V_label_nonzero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hs:CompressedOrientation318.shift w≠0) (n:ℤ) (tau:E.Point)
    (ht:tau=0 ∨ tau=T 0)
    (he:transport curve_eq (CompressedTranslation318.V S w source)=(n-1) • P+tau) : n-1≠0 := by
  intro hn
  rw [hn,zero_zsmul,zero_add] at he
  have hh:=source_V_not_pure_torsion S w source hs
  rcases ht with ht|ht
  · exact hh.1 (he.trans ht)
  · exact hh.2 (he.trans ht)

section Group
variable {G A F:Type*} [AddCommGroup G] [AddCommGroup A] [Field F] [CharZero F]

/-- Pass the exact global labels through an actual group base change and
 actual local logarithm. The global generator need not be locally formal. -/
theorem mapped_log_relation (ψ:G→+A) (S:AddSubgroup A) (ell:S→+F)
    (P H Q tau:G) (n c:ℤ) (hH:H=n • P+tau) (hQ:Q=c • P) (htau:(2:ℤ) • tau=0)
    (hmH:ψ H∈S) (hmQ:ψ Q∈S) :
    (n:F)*ell ⟨ψ Q,hmQ⟩=(c:F)*ell ⟨ψ H,hmH⟩ := by
  apply TorsionSafeIndex318.logarithm_relation S ell (ψ P) (ψ H) (ψ Q) (ψ tau) n c hmH hmQ
  · rw [hH,map_add,map_zsmul]
  · rw [hQ,map_zsmul]
  · rw [←map_zsmul,htau,map_zero]

/-- The local log ratio is the embedded rational ratio of the actual
 integer labels, including zero numerator labels. -/
theorem mapped_log_ratio (ψ:G→+A) (S:AddSubgroup A) (ell:S→+F)
    (P H Q tau:G) (n c:ℤ) (hH:H=n • P+tau) (hQ:Q=c • P) (htau:(2:ℤ) • tau=0)
    (hmH:ψ H∈S) (hmQ:ψ Q∈S) (hn:n≠0) (hlog:ell ⟨ψ H,hmH⟩≠0) :
    ell ⟨ψ Q,hmQ⟩/ell ⟨ψ H,hmH⟩=((c:ℚ)/(n:ℚ):ℚ) := by
  have hc:=mapped_log_relation ψ S ell P H Q tau n c hH hQ htau hmH hmQ
  push_cast
  apply (div_eq_div_iff hlog (Int.cast_ne_zero.mpr hn)).mpr
  simpa only [mul_comm] using hc

end Group

end
end GlobalLogRatios318
#print axioms GlobalLogRatios318.source_V_label_nonzero
#print axioms GlobalLogRatios318.mapped_log_ratio
