module
public import PELOriginalHyperplanePullbackTopology318
public section
noncomputable section
namespace PELOriginalHyperplanePullbackHolomorphy318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalHyperplanePullback318 PELOriginalHyperplanePullbackTopology318
variable (τ:ℂ)(hτ:0<τ.im)(n:ℕ)
@[expose] def originalCoordinates(a:ComplexVectors)(p:PowerTotal τ hτ (n+2)):ComplexVectors×ℂ:=
  (chart τ hτ a p.1,((powerCore τ hτ (n+2)).localTriv a p).2)
@[expose] def pullbackCoordinates(a:ComplexVectors)(j:Label (n+2))(p:PullbackTotal τ hτ n):ComplexVectors×ℂ:=
  (chart τ hτ a p.1,((pullbackCore τ hτ n).localTriv j p).2)
@[expose] def forwardLocal(j:Label (n+2))(p:ComplexVectors×ℂ):ComplexVectors×ℂ:=
  (p.1,p.2/value τ hτ (n+2) j p.1)
@[expose] def inverseLocal(j:Label (n+2))(p:ComplexVectors×ℂ):ComplexVectors×ℂ:=
  (p.1,value τ hτ (n+2) j p.1*p.2)
lemma coefficient_original(a:ComplexVectors)(j:Label (n+2))(q:Base τ)
    (ha:q∈baseSet τ hτ a):
    sectionCoefficient τ hτ n a j q=value τ hτ (n+2) j (chart τ hτ a q):=by
  exact congrArg Prod.snd (local_formula τ hτ (n+2) (value τ hτ (n+2) j)
    (PELOriginalLevelPowerSections318.original_automorphy τ hτ (n+2) j) a q ha)

/-- Exact forward formula in genuine original source and pulled-back
hyperplane charts. The SAME section, not an unspecified unit, appears. -/
theorem forward_coordinate_identity(a:ComplexVectors)(j:Label (n+2))
    (p:PowerTotal τ hτ (n+2))(ha:p.1∈baseSet τ hτ a)
    (hj:p.1∈(pullbackCore τ hτ n).baseSet j):
    pullbackCoordinates τ hτ n a j (homeomorph τ hτ n p)=
      forwardLocal τ hτ n j (originalCoordinates τ hτ n a p):=by
  apply Prod.ext
  · rfl
  · change _=_/value τ hτ (n+2) j (chart τ hτ a p.1)
    rw [original_chart_ratio τ hτ n a p.1 ha j hj p.2]
    rw [←coefficient_original τ hτ n a j p.1 ha]
    rfl

theorem inverse_coordinate_identity(a:ComplexVectors)(j:Label (n+2))
    (p:PullbackTotal τ hτ n)(ha:p.1∈baseSet τ hτ a)
    (hj:p.1∈(pullbackCore τ hτ n).baseSet j):
    originalCoordinates τ hτ n a ((homeomorph τ hτ n).symm p)=
      inverseLocal τ hτ n j (pullbackCoordinates τ hτ n a j p):=by
  apply Prod.ext
  · rfl
  · exact (inverse_coordinate τ hτ n a j p ha hj).trans
      (congrArg (fun c:ℂ=>c*((pullbackCore τ hτ n).localTriv j p).2)
        (coefficient_original τ hτ n a j p.1 ha))

lemma forward_holomorphic(j:Label (n+2))(p:ComplexVectors×ℂ)
    (hp:value τ hτ (n+2) j p.1≠0):DifferentiableAt ℂ (forwardLocal τ hτ n j) p:=
  differentiableAt_fst.prodMk (differentiableAt_snd.div
    ((PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) j p.1).comp p differentiableAt_fst) hp)
lemma inverse_holomorphic(j:Label (n+2)):Differentiable ℂ (inverseLocal τ hτ n j):=
  differentiable_fst.prodMk
    (((PELOriginalLevelPowerSections318.holomorphic τ hτ (n+2) j).comp differentiable_fst).mul differentiable_snd)

/-- Both actual coordinate maps are holomorphic on EVERY genuine
bundle-chart overlap. Together with the constructed total homeomorphism,
complex-linear fiber maps and identity base square, this identifies the
actual hyperplane pullback with the SAME original L^(n+2). No embedding
of the original surface is required or asserted. -/
theorem actual_local_biholomorphy(a:ComplexVectors)(j:Label (n+2))
    (p:PowerTotal τ hτ (n+2))(ha:p.1∈baseSet τ hτ a)
    (hj:p.1∈(pullbackCore τ hτ n).baseSet j):
    DifferentiableAt ℂ (forwardLocal τ hτ n j) (originalCoordinates τ hτ n a p)∧
    DifferentiableAt ℂ (inverseLocal τ hτ n j)
      (pullbackCoordinates τ hτ n a j (homeomorph τ hτ n p)):=by
  refine ⟨forward_holomorphic τ hτ n j _ ?_,inverse_holomorphic τ hτ n j _⟩
  change value τ hτ (n+2) j (chart τ hτ a p.1)≠0
  rw [←coefficient_original τ hτ n a j p.1 ha]
  exact coefficient_ne τ hτ n a j p.1 hj
end PELOriginalHyperplanePullbackHolomorphy318
