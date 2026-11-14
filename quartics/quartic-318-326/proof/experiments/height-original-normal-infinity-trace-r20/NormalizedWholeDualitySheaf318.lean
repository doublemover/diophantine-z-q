module
public import NormalizedWholeDualityFrames318
public import NormalizedWholeGluing318
public import GenericOpenPushout318
public import ClutchedModuleFrames318
public import OpenClutchedLocallyFree318
public import ActualOpenImmersionLineFrame318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace NormalizedWholeDualitySheaf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizedReciprocalLaurent318 NormalizedWholeOverlap318 NormalizedWholeOpenMaps318
open NormalizedWholeGluing318
universe u
set_option maxHeartbeats 1800000
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)

lemma gluing_square : intoInfinity R d a ≫ infinityChart R d a=
    intoFinite R d a ≫ finiteChart R d a := (pushout.condition).symm
lemma finite_range : (finiteChart R d a) ⁻¹ᵁ (infinityChart R d a).opensRange=
    (intoFinite R d a).opensRange := by
  ext x
  change (finiteChart R d a x∈Set.range (infinityChart R d a)) ↔ x∈Set.range (intoFinite R d a)
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,hz,_⟩ := GenericOpenPushout318.exists_overlap
      (intoFinite R d a) (intoInfinity R d a) x y hy.symm
    exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    exact ⟨intoInfinity R d a z,congrArg (fun f => f z) (gluing_square R d a)⟩
lemma infinity_range : (infinityChart R d a) ⁻¹ᵁ (finiteChart R d a).opensRange=
    (intoInfinity R d a).opensRange := by
  ext x
  change (infinityChart R d a x∈Set.range (finiteChart R d a)) ↔ x∈Set.range (intoInfinity R d a)
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,_,hz⟩ := GenericOpenPushout318.exists_overlap
      (intoFinite R d a) (intoInfinity R d a) y x hy
    exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    exact ⟨intoFinite R d a z,congrArg (fun f => f z) (gluing_square R d a).symm⟩

/-- The coefficient gluing convention is LEFT = transition*RIGHT.
Since the actual dual-plus-differential GENERATOR changes by -t^-2,
the actual coefficient transition is its inverse, -t². -/
@[expose] def overlapUnit : (CommonOrder R d a)ˣ :=
  Units.map (algebraMap (Laurent R) (CommonOrder R d a)) (-(coordinate R)^2)
@[expose] def sectionUnit : Γ(overlap R d a,⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (CommonOrder R d a))).inv.hom (overlapUnit R d a)

/-- A genuine globally defined module sheaf on the SAME entire proper
model. The finite dual/coordinate generator calculation fixes its actual
transition; the Grothendieck dualizing identification is still separate. -/
@[expose] def line : (scheme R d a).Modules :=
  ClutchedModule318.sheaf (finiteChart R d a) (infinityChart R d a)
    (intoFinite R d a) (intoInfinity R d a) (gluing_square R d a) (sectionUnit R d a).val

@[expose] def finiteFrame : (line R d a).restrict (finiteChart R d a) ≅
    SheafOfModules.unit (finiteScheme R d a).ringCatSheaf :=
  ClutchedModuleFrames318.firstFrame _ _ _ _ (gluing_square R d a) _
    (sectionUnit R d a).isUnit (infinity_range R d a)
@[expose] def infinityFrame : (line R d a).restrict (infinityChart R d a) ≅
    SheafOfModules.unit (infinityScheme R d a).ringCatSheaf :=
  ClutchedModuleFrames318.secondFrame _ _ _ _ (gluing_square R d a) _ (finite_range R d a)

/-- The local identifications retain the actual ENTIRE finite-dual
modules and their correct order actions through the real tilde functor. -/
@[expose] def finiteDualIso : (line R d a).restrict (finiteChart R d a) ≅
    tilde (R:=CommRingCat.of (FiniteOrder R d a))
      (ModuleCat.of (FiniteOrder R d a) (NormalizedWholeDualityFrames318.FiniteDual R d a)) :=
  finiteFrame R d a ≪≫ tildeSelf.symm ≪≫
    (tilde.functor (CommRingCat.of (FiniteOrder R d a))).mapIso
      (NormalizedWholeDualityFrames318.finiteFrame R d a).toModuleIso
@[expose] def infinityDualIso : (line R d a).restrict (infinityChart R d a) ≅
    tilde (R:=CommRingCat.of (InfinityOrder R d a))
      (ModuleCat.of (InfinityOrder R d a) (NormalizedWholeDualityFrames318.InfinityDual R d a)) :=
  infinityFrame R d a ≪≫ tildeSelf.symm ≪≫
    (tilde.functor (CommRingCat.of (InfinityOrder R d a))).mapIso
      (NormalizedWholeDualityFrames318.infinityFrame R d a).toModuleIso

lemma cover_top : (finiteChart R d a).opensRange ⊔ (infinityChart R d a).opensRange=⊤ := by
  apply top_unique
  intro x hx
  rcases charts_cover R d a x with h|h
  · exact Or.inl h
  · exact Or.inr h

@[expose] def cover : ULift.{u} Bool → (scheme R d a).Opens :=
  OpenClutchedLocallyFree318.cover (finiteChart R d a).opensRange (infinityChart R d a).opensRange
@[expose] def openFrame (i : ULift.{u} Bool) :
    SheafOfModules.free (R:=(cover R d a i).toScheme.ringCatSheaf) PUnit.{u+1} ≅
      (line R d a).restrict (cover R d a i).ι := by
  rcases i with ⟨i⟩
  cases i
  · exact OpenClutchedLocallyFree318.freeUnit _ ≪≫
      ActualOpenImmersionLineFrame318.ambientFrame (finiteChart R d a) (line R d a) (finiteFrame R d a).symm
  · exact OpenClutchedLocallyFree318.freeUnit _ ≪≫
      ActualOpenImmersionLineFrame318.ambientFrame (infinityChart R d a) (line R d a) (infinityFrame R d a).symm

/-- Produced singleton local generating frames on a genuine whole cover. -/
theorem locallyFree : (line R d a).IsLocallyFree :=
  ModuleFreeOpenFrames318.locallyFree (line R d a) PUnit.{u+1} (cover R d a)
    (OpenClutchedLocallyFree318.cover_top _ _ (cover_top R d a)) (openFrame R d a)
end NormalizedWholeDualitySheaf318
