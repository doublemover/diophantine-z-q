module
public import UnitFrameSectionDetection318
public import WeierstrassAffineInvariant318
public import CompletedIntegral318
public section
noncomputable section
namespace WeierstrassAffineFormCancellation318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u
variable {R:Type u} [CommRing R] [IsDomain R] (A B:R)
abbrev S:=ShortAffineJacobian318.Ring A B
abbrev X:=WeierstrassGluing318.scheme A B
abbrev U:=WeierstrassAffineInvariant318.finiteOpen A B
local instance integral : IsIntegral (X A B):=CompletedIntegral318.completed_integral A B

/-- The actual whole finite chart is nonempty, over any domain base. -/
theorem finite_nonempty : Nonempty (U A B):=by
  letI:=AffineCoordinateDomain318.affine_domain A B
  obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (S A B))))
  exact ⟨⟨WeierstrassGluing318.finiteChart A B p,⟨p,trivial,rfl⟩⟩⟩
local instance nonempty : Nonempty (U A B):=finite_nonempty A B

@[expose] def scalar : S A B→+*Γ(X A B,U A B):=
  ((WeierstrassGluing318.finiteChart A B).appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (S A B))).inv.hom

theorem scalar_apply (r:S A B):scalar A B r=
    ((WeierstrassGluing318.finiteChart A B).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (S A B))).inv r):=rfl

theorem scalar_injective : Function.Injective (scalar A B):=
  (ConcreteCategory.bijective_of_isIso ((WeierstrassGluing318.finiteChart A B).appIso ⊤).inv).1.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (S A B))).inv).1

/-- Cancellation in actual finite Kaehler differentials follows from the
proved whole-scheme intrinsic frame, not an assumed torsion-free module. -/
theorem cancel_scalar (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (r:S A B) (hr:r≠0) (a b:KaehlerDifferential R (S A B)) (h:r • a=r • b):a=b:=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective
    (WeierstrassGluing318.finiteChart A B) (WeierstrassGluing318.structureMap A B)
      (WeierstrassAffineInvariant318.finite_structure A B)).1
  apply UnitFrameSectionDetection318.cancel_scalar (IntrinsicGlobalFrame318.frame A B hD)
    (U A B) (scalar A B r) (by simpa only [map_zero] using (scalar_injective A B).ne hr)
  rw [scalar_apply]
  have he:=congrArg (IntrinsicChartSections318.sectionMap (WeierstrassGluing318.finiteChart A B)
      (WeierstrassGluing318.structureMap A B)
        (WeierstrassAffineInvariant318.finite_structure A B)) h
  rw [IntrinsicChartSections318.section_smul,IntrinsicChartSections318.section_smul] at he
  exact he

/-- Equality of actual global intrinsic forms is detected on the whole finite
chart, using the proved global frame and integral completion. -/
theorem restrict_injective (hD:IsUnit (-16*(4*A^3+27*B^2))):
    Function.Injective ((FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show U A B≤⊤ from le_top)).op):=
  UnitFrameSectionDetection318.restrict_injective (IntrinsicGlobalFrame318.frame A B hD)
    (U A B) ⊤ le_top
end WeierstrassAffineFormCancellation318
