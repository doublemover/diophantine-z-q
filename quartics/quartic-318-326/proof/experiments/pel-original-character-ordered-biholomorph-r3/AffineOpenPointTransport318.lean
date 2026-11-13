module
public import Mathlib.AlgebraicGeometry.AffineScheme
public section
noncomputable section
namespace AffineOpenPointTransport318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y:Scheme.{u}}

lemma fromSpec_injective {U:X.Opens} (hU:IsAffineOpen U):
    Function.Injective hU.fromSpec:=hU.fromSpec.isOpenEmbedding.injective

lemma exists_prime {U:X.Opens} (hU:IsAffineOpen U) (x:X) (hx:x∈U):
    ∃P:Spec Γ(X,U),hU.fromSpec P=x:=by
  have hh:x∈Set.range hU.fromSpec:=by rwa [hU.range_fromSpec]
  exact hh

/-- Point-level equality of the actual affine-open section map and the
original scheme morphism, obtained from the native scheme square. -/
lemma appLE_point (f:X⟶Y) {U:Y.Opens} {V:X.Opens}
    (hU:IsAffineOpen U) (hV:IsAffineOpen V) (e:V≤f⁻¹ᵁU)
    (P:Spec Γ(X,V)):
    hU.fromSpec (Spec.map (f.appLE U V e) P)=f (hV.fromSpec P):=by
  exact congrArg (fun k:Spec Γ(X,V)⟶Y=>k P)
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e)

lemma app_point (f:X⟶Y) {U:Y.Opens} (hU:IsAffineOpen U)
    (hV:IsAffineOpen (f⁻¹ᵁU)) (P:Spec Γ(X,f⁻¹ᵁU)):
    hU.fromSpec (Spec.map (f.app U) P)=f (hV.fromSpec P):=by
  simpa only [Scheme.Hom.appLE_eq_app] using appLE_point f hU hV le_rfl P
end AffineOpenPointTransport318
