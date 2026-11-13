module
public import FiniteNormalOpenImage318
public import NormalAffineBasis318
public import FunctionFieldGluing318
public section
noncomputable section
namespace FiniteNormalAllOpenImage318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f:X⟶Y) [IsFinite f] [IsDominant f]

/-- A normal affine basis upgrades the actual affine image theorem to
EVERY nonempty target open. The local target sections are glued by their
one common native generic germ; the full inverse-image sections remain. -/
theorem range_iff (basis:NormalAffineBasis318.HasBasis Y)
    (U:Y.Opens) [Nonempty U] [Nonempty (f⁻¹ᵁU)] (x:Γ(X,f⁻¹ᵁU)):
    x∈Set.range (f.app U).hom ↔
      X.germToFunctionField (f⁻¹ᵁU) x∈Set.range (DominantFunctionField318.map f).hom:=by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨Y.germToFunctionField U a,
      congrArg (fun k:Γ(Y,U)⟶X.functionField=>k a)
        (DominantFunctionField318.map_germ f U)⟩
  · rintro ⟨z,hz⟩
    choose V hVU hpoint hAffine hNormal using basis U
    letI (p:U):Nonempty (V p):=⟨⟨p.val,hpoint p⟩⟩
    letI (p:U):Nonempty (f⁻¹ᵁV p):=DominantFunctionField318.preimage_nonempty f (V p)
    let s (p:U):Γ(X,f⁻¹ᵁV p):=
      X.presheaf.map (homOfLE (f.preimage_mono (hVU p))).op x
    have hs (p:U):X.germToFunctionField (f⁻¹ᵁV p) (s p)=
        X.germToFunctionField (f⁻¹ᵁU) x:=
      AffineDominantNormRestriction318.germ_restrict X _ x
    have localLift:∀p:U,∃a:Γ(Y,V p),(f.app (V p)).hom a=s p:=by
      intro p
      letI:IsIntegrallyClosed Γ(Y,V p):=hNormal p
      apply (FiniteNormalOpenImage318.range_iff f (V p) (hAffine p) (s p)).mpr
      exact ⟨z,hz.trans (hs p).symm⟩
    choose a ha using localLift
    have germ_a:∀p:U,Y.germToFunctionField (V p) (a p)=z:=by
      intro p
      apply (DominantFunctionField318.map f).hom.injective
      have square:=congrArg (fun k:Γ(Y,V p)⟶X.functionField=>k (a p))
        (DominantFunctionField318.map_germ f (V p))
      exact square.trans ((congrArg (X.germToFunctionField (f⁻¹ᵁV p)) (ha p)).trans
        ((hs p).trans hz.symm))
    have cover:U≤iSup V:=by
      intro p hp
      exact Opens.mem_iSup.mpr ⟨⟨p,hp⟩,hpoint ⟨p,hp⟩⟩
    obtain ⟨a0,ha0⟩:=FunctionFieldGluing318.exists_section Y V U
      (fun p=>homOfLE (hVU p)) cover a z germ_a
    refine ⟨a0,?_⟩
    apply X.germToFunctionField_injective (f⁻¹ᵁU)
    have square:=congrArg (fun k:Γ(Y,U)⟶X.functionField=>k a0)
      (DominantFunctionField318.map_germ f U)
    exact square.symm.trans ((congrArg (DominantFunctionField318.map f) ha0).trans hz)
end FiniteNormalAllOpenImage318
