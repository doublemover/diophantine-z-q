module
public import PELOriginalDiscreteSLGroup318
public section
noncomputable section
namespace PELPrincipalProperAction318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 PELJointPeriodFamily318
open PELJointArithmeticLift318 PELJointArithmeticCoherence318 PELPrincipalThreeFreeAction318
open PELOriginalDiscreteSLGroup318
set_option maxHeartbeats 1400000

/-- A continuous equivariant map to a proper-discontinuous action detects
finiteness of every compact transporter. It need not be injective on points;
the arithmetic group map itself must be injective. -/
theorem proper_of_equivariant {G H X Y : Type*} [Group G] [Group H]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X] [MulAction H Y]
    [ProperlyDiscontinuousSMul H Y] (φ : G →* H) (hφ : Function.Injective φ)
    (f : X → Y) (hf : Continuous f) (he : ∀ g x,f (g • x)=φ g • f x) :
    ProperlyDiscontinuousSMul G X where
  finite_disjoint_inter_image := by
    intro K L hK hL
    have hfin := finite_disjoint_inter_image (Γ:=H) (hK.image hf) (hL.image hf)
    apply (hfin.preimage (f:=φ) hφ.injOn).subset
    rintro g ⟨z,⟨⟨x,hx,rfl⟩,hz⟩⟩
    refine ⟨f (g • x),⟨?_,⟨g • x,hz,rfl⟩⟩⟩
    exact ⟨f x,⟨x,hx,rfl⟩,(he g x).symm⟩

instance : MulAction principalThree HalfPlane where
  smul u τ := nextParameter u.val (determinant u) τ
  one_smul τ := congrArg Prod.fst (lift_one (τ,(0:ComplexVectors)))
  mul_smul u v τ := (congrArg Prod.fst
    (lift_mul u.val v.val (determinant u) (determinant v) (τ,(0:ComplexVectors)))).symm

@[expose] def toUpper (τ : HalfPlane) : UpperHalfPlane := ⟨τ,τ.property⟩

theorem toUpper_continuous : Continuous toUpper :=
  UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val

/-- Exact match with Mathlib's standard SL2(R) action is checked on the
same complex coordinate, not inferred from an abstract group isomorphism. -/
theorem toUpper_equivariant (u : principalThree) (τ : HalfPlane) :
    toUpper (u • τ)=intoImage u • toUpper τ := by
  apply UpperHalfPlane.ext
  change QuaternionicUnitPeriodTransport318.unitParameter
    PELQuaternionRealRepresentation318.representation PELPrincipalOrderCoordinates318.order u.val τ=
      ((specialLinear u • toUpper τ:UpperHalfPlane):ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

instance base_proper : ProperlyDiscontinuousSMul principalThree HalfPlane :=
  proper_of_equivariant intoImage intoImage_injective toUpper toUpper_continuous toUpper_equivariant

/-- Proper discontinuity of the actual JOINT family action follows from
its continuous equivariant base projection and the constructed discrete group. -/
instance total_proper : ProperlyDiscontinuousSMul principalThree Total :=
  proper_of_equivariant intoImage intoImage_injective (fun p : Total => toUpper p.1)
    (toUpper_continuous.comp continuous_fst) (fun u p => toUpper_equivariant u p.1)
end PELPrincipalProperAction318
