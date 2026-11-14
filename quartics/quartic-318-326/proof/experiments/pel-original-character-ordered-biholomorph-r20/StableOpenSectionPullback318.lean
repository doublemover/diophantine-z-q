module
public import AffineDominantNormRestriction318
public section
noncomputable section
namespace StableOpenSectionPullback318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}}

/-- Literal scheme-section pullback, followed by the ACTUAL restriction
back to a forward-stable open. No generic-field transported map is used. -/
@[expose] def sectionPullback (f:X⟶X) (U:X.Opens) (h:U≤f⁻¹ᵁU):
    Γ(X,U)→+*Γ(X,U):=(f.appLE U U h).hom

variable [IsIntegral X] (f:X⟶X) [IsDominant f]
lemma germ_sectionPullback (U:X.Opens) [Nonempty U] (h:U≤f⁻¹ᵁU)
    (x:Γ(X,U)):
    X.germToFunctionField U (sectionPullback f U h x)=
      DominantFunctionField318.map f (X.germToFunctionField U x):=by
  letI:=DominantFunctionField318.preimage_nonempty f U
  change X.germToFunctionField U
    (X.presheaf.map (homOfLE h).op (f.app U x))=_
  rw [AffineDominantNormRestriction318.germ_restrict]
  exact (congrArg (fun k:Γ(X,U)⟶X.functionField=>k x)
    (DominantFunctionField318.map_germ f U)).symm

/-- All actual restriction maps commute with the stable-open action,
including an empty smaller open. -/
lemma restriction_square {U V:X.Opens} (j:U⟶V)
    (hU:U≤f⁻¹ᵁU) (hV:V≤f⁻¹ᵁV) (x:Γ(X,V)):
    sectionPullback f U hU (X.presheaf.map j.op x)=
      X.presheaf.map j.op (sectionPullback f V hV x):=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:Nonempty V:=by obtain ⟨p⟩:=h;exact ⟨⟨p.val,j.le p.property⟩⟩
    apply X.germToFunctionField_injective U
    rw [germ_sectionPullback,AffineDominantNormRestriction318.germ_restrict,
      AffineDominantNormRestriction318.germ_restrict,germ_sectionPullback]
  · have hu:U=⊥:=by
      apply le_antisymm _ bot_le
      intro p hp
      exact (h ⟨⟨p,hp⟩⟩).elim
    haveI:Subsingleton Γ(X,U):=by rw [hu];infer_instance
    exact Subsingleton.elim _ _
end StableOpenSectionPullback318
