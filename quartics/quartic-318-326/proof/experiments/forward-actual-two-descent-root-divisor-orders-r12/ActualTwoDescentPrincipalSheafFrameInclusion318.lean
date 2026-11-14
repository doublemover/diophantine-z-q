module
public import ActualTwoDescentIdealInclusionRestrictionSquare318
public section
noncomputable section
namespace ActualTwoDescentPrincipalSheafFrameInclusion318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentTildeStructureNormalization318 ActualTwoDescentIdealInclusionRestrictionSquare318
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (g : R) (e : R ≃ₗ[R] I)
    (he : ∀ a, (e a : R)=a*g)

def frame : tilde (ModuleCat.of R I) ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  (tilde.functor (CommRingCat.of R)).mapIso e.symm.toModuleIso ≪≫ tildeSelf

lemma frame_global (x : I) :
    (frame I e).hom.app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (e.symm x) := by
  have h := (tilde.toTildeΓNatIso (R:=CommRingCat.of R)).hom.naturality e.symm.toModuleIso.hom
  have hx := congrArg (fun f => f x) h.symm
  change (tilde.map e.symm.toModuleIso.hom).app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)=
    (tilde.isoTop (ModuleCat.of R R)).hom (e.symm x) at hx
  exact hx.trans (isoTop_ring (e.symm x))

include he in
/-- The actual ideal inclusion is the actual frame followed by
multiplication by its specified generator. This is a whole sheaf equality. -/
lemma frame_inclusion : inclusion I=(frame I e).hom ≫
    ClutchedModule318.multiply ((Scheme.ΓSpecIso (CommRingCat.of R)).inv g) := by
  apply tilde_hom_ext
  intro x
  change (inclusion I).app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)=
    (ClutchedModule318.multiply _).app ⊤ ((frame I e).hom.app ⊤
      ((tilde.isoTop (ModuleCat.of R I)).hom x))
  rw [inclusion_global,ClutchedModule318.multiply_top,frame_global,←map_mul]
  congr 1
  have h := he (e.symm x)
  rw [e.apply_symm_apply] at h
  exact h

include he in
lemma frame_inclusion_apply (U : (Spec (CommRingCat.of R)).Opens)
    (x : Γ(tilde (ModuleCat.of R I),U)) :
    (inclusion I).app U x=(frame I e).hom.app U x*
      ((Spec (CommRingCat.of R)).presheaf.map
        (CategoryTheory.homOfLE (show U≤⊤ from le_top)).op
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv g)) := by
  rw [frame_inclusion I g e he]
  exact ClutchedModule318.multiply_apply _ U _
end ActualTwoDescentPrincipalSheafFrameInclusion318
