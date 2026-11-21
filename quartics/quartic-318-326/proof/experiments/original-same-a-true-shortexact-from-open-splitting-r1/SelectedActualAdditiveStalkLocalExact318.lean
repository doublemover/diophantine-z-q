module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Chartwise splitting supplies the genuine additive sheaf boundary

This uses the actual scheme-module restriction and the actual additive
presheaf stalks. An open cover suffices: there is no general assertion
of exactness of the closed-fibre pullback or of any tilde functor.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

namespace SelectedActualAdditiveStalkLocalExact318

universe u v
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

private instance underlyingPresheafAdditive (X : Scheme.{u}) :
    (Scheme.Modules.toPresheaf X).Additive := by
  change (Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.toPresheaf X.ringCatSheaf.obj).Additive
  letI : (Scheme.Modules.toPresheafOfModules X).Additive := inferInstanceAs
    (SheafOfModules.forget.{u} X.ringCatSheaf).Additive
  infer_instance

/-- The actual restriction is additive because its actual comparison to
inverse image is a natural isomorphism, not because it is exact by fiat. -/
instance restrictionAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).Additive :=
  Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback j).symm

variable {X : Scheme.{u}} (S : ShortComplex X.Modules)


/-- The same concrete additive site used by the actual directional row
and its genuine Ext boundary. -/
abbrev actualAdditive (X : Scheme.{u}) : X.Modules ⥤
    Sheaf (_root_.Opens.grothendieckTopology (X : TopCat.{u})) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance (X : Scheme.{u}) : (actualAdditive X).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms

/-- The row on the additive sheaves of the same actual modules. -/
@[expose] def additiveRow := S.map (actualAdditive X)

variable [HasSheafify (_root_.Opens.grothendieckTopology (X : TopCat.{u})) AddCommGrpCat.{u}]

private abbrev AStalk (x : X) :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

private theorem actualStalkShortExact
    {I : Type v} (W : I → Scheme.{u}) (j : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hCover : ∀ x : X, ∃ (i : I) (y : W i), j i y = x)
    (hSplit : ∀ i, Nonempty ((S.map (Scheme.Modules.restrictFunctor (j i))).Splitting))
    (x : X) : ((additiveRow S).map (AStalk x)).ShortExact := by
  obtain ⟨i, y, rfl⟩ := hCover x
  obtain ⟨b⟩ := hSplit i
  let Fl := Scheme.Modules.toPresheaf (W i) ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let Fr : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j i y)
  have hb : (S.map (Scheme.Modules.restrictFunctor (j i) ⋙ Fl)).ShortExact := (b.map Fl).shortExact
  have ec : Scheme.Modules.restrictFunctor (j i) ⋙ Fl ≅ Fr :=
    Scheme.Modules.restrictStalkNatIso (j i) y
  have h := ShortComplex.shortExact_of_iso (S.mapNatIso ec) hb
  simpa only [additiveRow, actualAdditive, ← ShortComplex.map_comp, Fr, Scheme.Modules.toPresheaf,
    Scheme.Modules.toPresheafOfModules, SheafOfModules.toSheaf, TopCat.Sheaf.forget] using h

/-- An actual open cover on which this very module complex splits produces
the additive short-exact hypothesis for the actual global boundary. No
abstract exact complex dependent on a choice of component is introduced. -/
theorem short_exact_of_open_splitting
    {I : Type v} (W : I → Scheme.{u}) (j : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hCover : ∀ x : X, ∃ (i : I) (y : W i), j i y = x)
    (hSplit : ∀ i, Nonempty ((S.map (Scheme.Modules.restrictFunctor (j i))).Splitting)) :
    (additiveRow S).ShortExact := by
  let R := additiveRow S
  let h := actualStalkShortExact S W j hCover hSplit
  apply ShortComplex.ShortExact.mk'
  · exact (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact R).2 (fun x => (h x).exact)
  · let L := ShortComplex.mk (0 : R.X₁ ⟶ R.X₁) R.f (by simp)
    apply (L.exact_iff_mono rfl).mp
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact L).2
    intro x
    apply ((L.map (AStalk x)).exact_iff_mono (by simp [L])).mpr
    exact (h x).mono_f
  · let P := ShortComplex.mk R.g (0 : R.X₃ ⟶ R.X₃) (by simp)
    apply (P.exact_iff_epi rfl).mp
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact P).2
    intro x
    apply ((P.map (AStalk x)).exact_iff_epi (by simp [P])).mpr
    exact (h x).epi_g

end SelectedActualAdditiveStalkLocalExact318
