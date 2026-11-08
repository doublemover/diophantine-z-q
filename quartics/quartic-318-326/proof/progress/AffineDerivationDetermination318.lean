module
public import LocalizationDerivation318
public import FamilyIntrinsicDifferentials318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace AffineDerivationDetermination318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- The additive underlying natural transformation of an actual sheaf derivation. -/
@[expose] def additiveMap {X : Scheme.{u}} {C : X.Opensᵒᵖ ⥤ CommRingCat.{u}}
    {φ : C ⟶ X.presheaf} {M : X.Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) :
    X.presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ M.presheaf where
  app U := AddCommGrpCat.ofHom d.d
  naturality {U V} f := by
    ext a
    exact d.d_map f a

/-- On an affine scheme a sheaf-valued derivation is determined by its action on
actual global regular functions. Localized denominator cancellation proves the
basic-open case, and the actual sheaf separation axiom gives every open. -/
theorem ext_top {S : CommRingCat.{u}}
    {C : (Spec S).Opensᵒᵖ ⥤ CommRingCat.{u}} {φ : C ⟶ (Spec S).presheaf}
    {M : (Spec S).Modules}
    (d e : PresheafOfModulesOfCommRing.Derivation' M.val φ)
    (h : ∀ a : Γ(Spec S,⊤), d.d a=e.d a) : d=e := by
  have hb (s : S) :
      (additiveMap d).app (op (PrimeSpectrum.basicOpen s)) =
        (additiveMap e).app (op (PrimeSpectrum.basicOpen s)) := by
    apply AddCommGrpCat.hom_ext
    apply LocalizationDerivation318.additive_ext
      (T:=Γ(Spec S,PrimeSpectrum.basicOpen s))
      (M:=Γ(M,PrimeSpectrum.basicOpen s)) (Submonoid.powers s)
      (d.d (X:=op (PrimeSpectrum.basicOpen s))) (e.d (X:=op (PrimeSpectrum.basicOpen s)))
      (fun a b => d.d_mul a b) (fun a b => e.d_mul a b)
    intro a
    change d.d ((Spec S).presheaf.map (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso S).inv a)) =
      e.d ((Spec S).presheaf.map (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso S).inv a))
    exact (d.d_map (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso S).inv a)).trans
      ((congrArg (M.val.map (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op)
        (h ((Scheme.ΓSpecIso S).inv a))).trans
        (e.d_map (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso S).inv a)).symm)
  have hh : additiveMap d=additiveMap e :=
    TopCat.Sheaf.hom_ext _ ⟨M.presheaf,M.isSheaf⟩ PrimeSpectrum.isBasis_basic_opens hb
  ext U a
  exact congrArg (fun f => (f.app U) a) hh
end AffineDerivationDetermination318
