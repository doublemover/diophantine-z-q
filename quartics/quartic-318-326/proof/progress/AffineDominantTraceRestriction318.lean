module
public import AffineDominantTrace318
public section
noncomputable section
namespace AffineDominantTraceRestriction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
lemma germ_restrict (X:Scheme.{u}) [IsIntegral X] {U V:X.Opens}
    [Nonempty U] [Nonempty V] (i:U⟶V) (s:Γ(X,V)):
    X.germToFunctionField U (X.presheaf.map i.op s)=X.germToFunctionField V s:=by
  exact X.presheaf.germ_res_apply i _ _ s
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f]
    (hfinite:letI:=AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
/-- Actual restriction compatibility of the additive regular trace on
normal affine opens. Neither intersections nor test schemes are replaced
by point sets. -/
lemma restrict {U V:Y.Opens} (hU:IsAffineOpen U) (hV:IsAffineOpen V)
    [Nonempty U] [Nonempty V] [IsIntegrallyClosed Γ(Y,U)] [IsIntegrallyClosed Γ(Y,V)]
    (i:U⟶V) (s:Γ(X,f⁻¹ᵁV)):
    Y.presheaf.map i.op (AffineDominantTrace318.trace f V hV hfinite s)=
      AffineDominantTrace318.trace f U hU hfinite
        (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op s):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Nonempty (f⁻¹ᵁV):=DominantFunctionField318.preimage_nonempty f V
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  apply Y.germToFunctionField_injective U
  rw [germ_restrict,AffineDominantTrace318.embedding,AffineDominantTrace318.embedding,
    germ_restrict]
end AffineDominantTraceRestriction318
