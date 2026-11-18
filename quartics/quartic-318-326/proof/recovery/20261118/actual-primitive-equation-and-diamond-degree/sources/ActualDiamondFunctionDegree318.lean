module
public import IrreducibleUniformPrimitiveEquation318
public section
noncomputable section
namespace ActualDiamondFunctionDegree318
open TranscendentalJGenericFiber318 GenericMarkingOrbitField318
open GenericPrimitiveXCoordinate318 UniformTranscendentalPrimitiveEquation318
open IrreducibleUniformPrimitiveEquation318 WeierstrassCurve.Affine
variable (N:ℕ) [NeZero N]

private def castP {A B:WeierstrassCurve.Affine ℂ} (h:A=B) : A.Point ≃+ B.Point := by
  subst B
  exact AddEquiv.refl _

private theorem cast_x {A B:WeierstrassCurve.Affine ℂ} (h:A=B) (P:A.Point) :
    valueX (castP h P)=valueX P := by subst B;rfl

variable (L:Type*) [Field L] [Algebra (K N) L] [FiniteDimensional (K N) L] [IsGalois (K N) L]

/-- An embedding of the actual finite field of definition transports its
geometric points, not only their degree. Consequently this is true for
*every* such L, without specifying a simultaneous splitting field. -/
theorem annihilates (Q:Polynomial (K N)) (hs:rootsSpec N Q) (P:A N L) (hp:addOrderOf P=N) :
    Polynomial.aeval (x N L P) Q=0 := by
  obtain ⟨τ,_,ha,ht⟩ := exists_period 0
  let e := embedding N τ ha ht
  letI : Algebra (K N) ℂ := e.toAlgebra
  let φ : L →ₐ[K N] ℂ := IsAlgClosed.lift
  let eqW := congrArg WeierstrassCurve.toAffine (actual_curve N τ ha ht)
  let v := (castP eqW).toAddMonoidHom.comp (Point.map (W':=W N) φ)
  have hv := (castP eqW).injective.comp (Point.map_injective (W':=W N) φ)
  have hx : valueX (v P)=φ (x N L P) := by
    change valueX (castP eqW (Point.map (W':=W N) φ P))=_
    rw [cast_x]
    cases P <;> simp [valueX,x,Point.map_zero,Point.map_some]
  have he := (hs τ ha ht _).mpr ⟨⟨v P,(addOrderOf_injective v hv P).trans hp⟩,hx⟩
  apply φ.injective
  rw [←Polynomial.aeval_algHom_apply,map_zero]
  exact he

/-- The arithmetic diamond field of an actual primitive x-coordinate
satisfies the index estimate with no remaining polynomial or monodromy
hypothesis. This does *not* assert that a named modular-curve model
already has this precise field as its function field. -/
theorem degree (hN:1<N) (P:A N L) (hp:addOrderOf P=N) (H:Subgroup (ZMod N)ˣ) :
    ∃ c:∀u:H,minpoly (K N) (x N L P)=minpoly (K N) (XP N L P H u),
      (Module.finrank (K N) (invariantField N L P H c):ℝ) ≤
        (N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  obtain ⟨Q,_,_,hi,hs⟩ := exists_equation N hN
  let ann := annihilates N L Q hs
  exact ⟨PrimitiveXEquationDegree318.common_minpoly N L P hp H Q hi ann,
    PrimitiveXEquationDegree318.degree N L P hp H Q hi ann⟩
end ActualDiamondFunctionDegree318
