module
public import PELOriginalPrimitiveFixedCoordinates318
public import PELOriginalBaseCompact318
public section
noncomputable section
namespace PELOriginalBranchFiniteRepresentatives318
open QuaternionicJointPeriodTopology318 PELPrincipalOrderCoordinates318
open PELQuaternionRealRepresentation318 PELLevelThreeSimilitudes318
open PELIntegralEllipticObstructions318 QuaternionicFixedParameter318
open PELUnlevelledComplexBase318 PELOriginalElementaryAction318
open PELOriginalFixedIntegralCoordinates318 PELOriginalPrimitiveFixedCoordinates318
open PELDirichletHeight318 PELJointNormOneAction318
set_option maxHeartbeats 2400000

/-- Every actual nontrivial stabilizer point has a SAME-COARSE-POINT
representative in the finite list. The primitive integral element, positive
rotation coordinate, original norm and minimizing representative are all
constructed from that point. No genus, Euler or RH input is used. -/
theorem original_branch_representative (x : UnlevelledBase)
    (v : InertiaLabels318.V) (hv : v≠0)
    (hx : Multiplicative.ofAdd v • x=x) :
    ∃ (τ : HalfPlane) (a : Coordinates) (i : Fin 5),
      projection τ=x ∧ trace a=0 ∧
      integralNorm a=(PELFixedNormalizerFiniteSearch318.norm i:ℤ) ∧
      0<rotationCoordinate a ∧ fixesLine (representation (embed a)) τ ∧
      ((rotationCoordinate a).toNat,(a 0).natAbs,(a 3).natAbs)∈
        PELFixedNormalizerFiniteSearch318.rows i := by
  obtain ⟨σ,rfl⟩ := projection_surjective x
  obtain ⟨u,hu⟩ := PELOriginalOrbitHeightMinimum318.original_minimum σ
  have hp : projection (u • σ)=projection σ := PELOriginalBaseCompact318.projection_unit u σ
  have hx' : PELUnlevelledNormalizerAction318.coarseAction
      (PELPositiveOrderNormalizer318.word v) (projection (u • σ))=projection (u • σ) := by
    rw [hp]
    exact hx
  obtain ⟨n,hn,ht,_⟩ := PELNontrivialFixedTraceZero318.fixed_trace_zero v hv (u • σ) hx'
  obtain ⟨a,i,ha,hi,hr,hf⟩ := positive_primitive_fixed n (u • σ) hn ht
  exact ⟨u • σ,a,i,hp,ha,hi,hr,hf,
    PELOriginalFixedPolygonSearch318.original_finite_list a ha i hi hr (u • σ) hf hu⟩
end PELOriginalBranchFiniteRepresentatives318
