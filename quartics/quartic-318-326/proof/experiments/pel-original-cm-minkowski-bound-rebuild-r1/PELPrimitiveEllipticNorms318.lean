module
public import PELIntegralEllipticObstructions318
public section
noncomputable section
namespace PELPrimitiveEllipticNorms318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELLevelThreeSimilitudes318
open PELIntegralEllipticObstructions318 PELActualOrderNormalizer318 PELNormalizerTraceIntegral318
set_option maxHeartbeats 2400000

/-- The actual integral conjugation trace forces norm divisibility of the
trace square. No unproved squarefree valuation lemma is substituted. -/
theorem norm_divides_trace_square (u : normalizer) (a : Coordinates)
    (ha : embed a=(u.val:B)) : integralNorm a∣trace a^2 := by
  obtain ⟨z,hz⟩ := conjugation_trace_integral u
  rw [←ha,original_trace,original_norm] at hz
  have hn : (integralNorm a:ℚ)≠0 := by
    rw [←original_norm,ha]
    exact PELQuaternionAnisotropy318.reducedNorm_ne_zero _ u.val.ne_zero
  have he : (trace a:ℚ)^2=(integralNorm a:ℚ)*(z:ℚ) := by
    exact ((div_eq_iff hn).mp hz).trans (mul_comm _ _)
  refine ⟨z,?_⟩
  exact_mod_cast he

/-- Exhaustive arithmetic under the derived support210, with strict
elliptic trace bound. Exceptional nonzero traces retain their exact norms. -/
theorem numerical_cases (N T : ℤ) (hN : 0<N) (hdiv : N∣210)
    (htrace : N∣T^2) (hbound : T^2<4*N) :
    T=0 ∨ (N=1 ∧ T^2=1) ∨ (N=2 ∧ T^2=4) ∨ (N=3 ∧ T^2=9) := by
  have hle : N≤210 := Int.le_of_dvd (by norm_num) hdiv
  have htlow : -28≤T := by nlinarith
  have hthigh : T≤28 := by nlinarith
  interval_cases N <;> norm_num at hdiv
  all_goals interval_cases T <;> norm_num at htrace hbound ⊢

/-- Every primitive positive normalizer with a strict elliptic trace bound
has tracezero and one of the FIVE original inertia norms. -/
theorem classification (u : normalizer) (a : Coordinates) (ha : embed a=(u.val:B))
    (hN : 0<integralNorm a) (hdiv : integralNorm a∣210)
    (hbound : trace a^2<4*integralNorm a) :
    trace a=0 ∧ ∃ i : Fin 5,integralNorm a=(PELInertiaNormalizerData318.discriminant i:ℤ) := by
  have ht : trace a=0 := by
    rcases numerical_cases _ _ hN hdiv (norm_divides_trace_square u a ha) hbound with ht|h1|h2|h3
    · exact ht
    · exact False.elim (discriminant_ne_neg_three a (by rw [h1.1,h1.2] <;> norm_num))
    · exact False.elim (discriminant_ne_neg_four a (by rw [h2.1,h2.2] <;> norm_num))
    · exact False.elim (discriminant_ne_neg_three a (by rw [h3.1,h3.2] <;> norm_num))
  refine ⟨ht,?_⟩
  obtain ⟨h3,h5,h7,h8⟩ := trace_zero_residues a ht
  have hle : integralNorm a≤210 := Int.le_of_dvd (by norm_num) hdiv
  generalize hname : integralNorm a=N at hN hdiv h3 h5 h7 h8 hle ⊢
  interval_cases N <;> norm_num at hdiv h3 h5 h7 h8
  all_goals first
    | exact ⟨0,by norm_num [PELInertiaNormalizerData318.discriminant]⟩
    | exact ⟨1,by norm_num [PELInertiaNormalizerData318.discriminant]⟩
    | exact ⟨2,by norm_num [PELInertiaNormalizerData318.discriminant]⟩
    | exact ⟨3,by norm_num [PELInertiaNormalizerData318.discriminant]⟩
    | exact ⟨4,by norm_num [PELInertiaNormalizerData318.discriminant]⟩
end PELPrimitiveEllipticNorms318
