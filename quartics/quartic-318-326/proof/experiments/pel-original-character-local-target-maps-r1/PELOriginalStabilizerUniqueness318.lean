module
public import PELNontrivialFixedTraceZero318
public section
noncomputable section
namespace PELOriginalStabilizerUniqueness318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicFixedParameter318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELPositiveOrderNormalizer318
open PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318 PELUnlevelledComplexBase318
open PELPrincipalThreeStabilizer318 PELRealRationalProportionality318 PELNontrivialFixedTraceZero318
open PELOriginalElementaryAction318 PELOriginalLabeledFixedOrbits318
set_option maxHeartbeats 1800000

/-- At EVERY point of the actual coarse curve there is at most one
nontrivial stabilizer in the faithful original16-group. -/
theorem unique_nonzero_stabilizer (x : UnlevelledBase) (v w : InertiaLabels318.V)
    (hv : v≠0) (hw : w≠0)
    (hfv : Multiplicative.ofAdd v • x=x) (hfw : Multiplicative.ofAdd w • x=x) : v=w := by
  obtain ⟨τ,rfl⟩ := projection_surjective x
  obtain ⟨n,hn,htn,hpn⟩ := fixed_trace_zero v hv τ hfv
  obtain ⟨m,hm,htm,hpm⟩ := fixed_trace_zero w hw τ hfw
  have hnl : fixesLine (PELPositiveNormalizerMobius318.matrix n) τ :=
    fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive n) τ τ.property)
      (congrArg Subtype.val hn)
  have hml : fixesLine (PELPositiveNormalizerMobius318.matrix m) τ :=
    fixesLine_of_mobius _ _
      (QuaternionicPositiveDeterminant318.denominator_nonzero _ (matrix_positive m) τ τ.property)
      (congrArg Subtype.val hm)
  have htnM : PELPositiveNormalizerMobius318.matrix n 0 0+PELPositiveNormalizerMobius318.matrix n 1 1=0 := by
    change representation (n.val:B) 0 0+representation (n.val:B) 1 1=0
    rw [representation_trace,htn] <;> norm_num
  have htmM : PELPositiveNormalizerMobius318.matrix m 0 0+PELPositiveNormalizerMobius318.matrix m 1 1=0 := by
    change representation (m.val:B) 0 0+representation (m.val:B) 1 1=0
    rw [representation_trace,htm] <;> norm_num
  have he := QuaternionicTraceZeroFixedLine318.proportional _ _ τ τ.property hnl hml htnM htmM
    (positive_trace_zero_lower_left _ (matrix_positive m) htmM)
  obtain ⟨q,hq,hqm⟩ := rational_proportional (n.val:B) (m.val:B) (Units.ne_zero n.val)
    (positive_trace_zero_imI (m.val:B) m.property.2 htm) _ he
  have hu : n.val=PELQuaternionNormParity318.scalarUnit (Units.mk0 q hq)*m.val := by
    apply Units.ext
    simpa only [Algebra.smul_def] using hqm
  have hp : PELPositiveOrderNormalizer318.parity n=PELPositiveOrderNormalizer318.parity m := by
    change PELQuaternionNormParity318.parityHom n.val=PELQuaternionNormParity318.parityHom m.val
    rw [hu,map_mul,PELInertiaRationalConjugacy318.scalar_parity,one_mul]
  rw [hpn,hpm] at hp
  exact congrArg Multiplicative.toAdd hp

/-- The full stabilizer law at each ORIGINAL displayed point is now
proved, not just the existence of a nontrivial fixed label. -/
theorem original_point_stabilizer_iff (i : Fin 5) (v : InertiaLabels318.V) :
    Multiplicative.ofAdd v • originalPoint i=originalPoint i ↔
      v=0 ∨ v=InertiaLabels318.fiveLabels i := by
  constructor
  · intro h
    by_cases hv : v=0
    · exact Or.inl hv
    · exact Or.inr (unique_nonzero_stabilizer _ v _ hv
        (InertiaLabels318.five_labels_nonzero i) h (original_label_fixes i))
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact original_label_fixes i
end PELOriginalStabilizerUniqueness318
