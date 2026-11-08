module
public import AffinePrincipalLineFrame318
public import AffineLineFrameCover318
public import OpenLineRestriction318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FiniteLineTargetNeighborhood318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 650000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) [IsFinite f] (M:X.Modules)
    {κ:Type u} (V:κ→X.Opens) (hc:(⊤:X.Opens)≤⨆i,V i)
    (frames:∀i,SheafOfModules.unit (V i).toScheme.ringCatSheaf≅M.restrict (V i).ι)
variable (U:Y.Opens) (hU:IsAffineOpen U)
local instance sectionAlgebra:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
include hU in
lemma sectionFinite:Module.Finite Γ(Y,U) Γ(X,f⁻¹ᵁU):=f.finite_app U hU
include hc frames hU in
/-- Every point of an affine target open has a smaller genuine target
principal neighborhood whose entire source inverse image trivializes the
original line sheaf. The only line hypothesis is its actual covering
unit frames, not an assumed finite/projective section-module statement. -/
lemma exists_frame (x:U):∃a:Γ(Y,U),x.1∈Y.basicOpen a ∧ Nonempty
    (SheafOfModules.unit (f⁻¹ᵁY.basicOpen a).toScheme.ringCatSheaf≅
      M.restrict (f⁻¹ᵁY.basicOpen a).ι):=by
  letI:=sectionFinite f U hU
  let hW:IsAffineOpen (f⁻¹ᵁU):=hU.preimage f
  let N:=M.restrict hW.fromSpec
  let W:κ→(Spec Γ(X,f⁻¹ᵁU)).Opens:=fun i=>hW.fromSpec⁻¹ᵁV i
  have hw:(⊤:(Spec Γ(X,f⁻¹ᵁU)).Opens)≤⨆i,W i:=OpenLineRestriction318.covers hW.fromSpec V hc
  let fr:∀i,SheafOfModules.unit (W i).toScheme.ringCatSheaf≅N.restrict (W i).ι:=
    fun i=>OpenLineRestriction318.frame hW.fromSpec M (V i) (frames i)
  letI:=AffineLineFrameCover318.locallyFree Γ(X,f⁻¹ᵁU) N W hw fr
  obtain ⟨hfp,hflat,hr⟩:=AffineLineFrameCover318.properties Γ(X,f⁻¹ᵁU) N W hw fr
  letI:=hfp
  letI:=hflat
  let p:PrimeSpectrum Γ(Y,U):=hU.primeIdealOf x
  obtain ⟨a,ha,⟨e⟩⟩:=FiniteTargetSheafFrame318.exists_frame Γ(Y,U) Γ(X,f⁻¹ᵁU) N hr p
  refine ⟨a,?_,?_⟩
  · have hp:hU.fromSpec p∈Y.basicOpen a:=by
      change p∈hU.fromSpec⁻¹ᵁY.basicOpen a
      rw [hU.fromSpec_preimage_basicOpen a]
      exact ha
    simpa only [p,IsAffineOpen.fromSpec_primeIdealOf] using hp
  · rw [f.preimage_basicOpen a]
    exact ⟨AffinePrincipalLineFrame318.frame (f⁻¹ᵁU) hW (f.app U a) M e⟩
end FiniteLineTargetNeighborhood318
