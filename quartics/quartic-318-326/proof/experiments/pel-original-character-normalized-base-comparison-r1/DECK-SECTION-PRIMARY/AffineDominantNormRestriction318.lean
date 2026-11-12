module
public import AffineDominantNorm318
public section
noncomputable section
namespace AffineDominantNormRestriction318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
lemma germ_restrict (X:Scheme.{u}) [IsIntegral X] {U V:X.Opens}
    [Nonempty U] [Nonempty V] (i:U⟶V) (s:Γ(X,V)):
    X.germToFunctionField U (X.presheaf.map i.op s)=X.germToFunctionField V s:=by
  exact X.presheaf.germ_res_apply i _ _ s
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f]
lemma restrict {U V:Y.Opens} (hU:IsAffineOpen U) (hV:IsAffineOpen V)
    [Nonempty U] [Nonempty V] [IsIntegrallyClosed Γ(Y,U)] [IsIntegrallyClosed Γ(Y,V)]
    (i:U⟶V) (s:Γ(X,f⁻¹ᵁV)):
    Y.presheaf.map i.op (AffineDominantNorm318.norm f V hV s)=
      AffineDominantNorm318.norm f U hU
        (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op s):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Nonempty (f⁻¹ᵁV):=DominantFunctionField318.preimage_nonempty f V
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  apply Y.germToFunctionField_injective U
  rw [germ_restrict,AffineDominantNorm318.embedding,AffineDominantNorm318.embedding,
    germ_restrict]
end AffineDominantNormRestriction318
