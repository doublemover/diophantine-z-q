module

public import SelectedSameAOldGlobalExactCotangent318

/-!
# Genuine sections lifting on every actual old affine chart

The already-produced splitting of the literal restricted old module
row gives a lift of each specified section on that exact open. This
does not apply a global-section functor to a bare sheaf epimorphism.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

namespace SelectedSameAOldAffineLocalLifts318

universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAOldMarkedCompositeZero318
open SelectedSameAOldGlobalExactCotangent318
open SelectedActualAdditiveStalkLocalExact318

variable {k T : Type u} [Field k] [CommRing T] [Algebra k T]
variable {A P : Scheme.{u}}
variable (p : P ⟶ Spec (CommRingCat.of T)) (i : A ⟶ P)
variable (a : A ⟶ Spec (CommRingCat.of k)) (x : T →ₐ[k] k)
variable (J : IsPullback i a p (Spec.map (CommRingCat.ofHom x.toRingHom)))

/-- Evaluating the geometric affine splitting gives a right inverse on
sections of the literal same preimage open, simultaneously for all sections. -/
theorem original_affine_sections_split [Smooth p]
    {U : P.Opens} (hU : IsAffineOpen U) :
    let S := (oldDirect p i a x J.w).map (actualAdditive A)
    let V := i ⁻¹ᵁ U
    ∃ s : S.X₃.obj.obj (op V) ⟶ S.X₂.obj.obj (op V),
      s ≫ S.g.hom.app (op V) = 𝟙 (S.X₃.obj.obj (op V)) := by
  letI : IsClosedImmersion i := original_closed p i a x J
  let V := i ⁻¹ᵁ U
  let B := Spec Γ(A, V)
  let j : B ⟶ A := (hU.preimage i).fromSpec
  letI : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (hU.preimage i).fromSpec)
  let R := Scheme.Modules.restrictFunctor j
  letI : R.Additive := restrictionAdditive j
  letI : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  let S := oldDirect p i a x J.w
  let S' := S.map R
  let Utop : B.Opens := ⊤
  let Ev : B.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf B ⋙ (evaluation _ _).obj (op Utop)
  have hImage : j ''ᵁ Utop = V := by
    change j ''ᵁ ⊤ = V
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply TopologicalSpace.Opens.ext
    change Set.range j = (V : Set A)
    exact (hU.preimage i).range_fromSpec
  have hS' : Nonempty S'.Splitting := original_split_on_affine p i a x J hU
  obtain ⟨sp⟩ := hS'
  have hh : Ev.map sp.s ≫ Ev.map S'.g = 𝟙 (Ev.obj S'.X₃) :=
    ((Ev.map_comp sp.s S'.g).symm.trans
      (congrArg (fun f : S'.X₃ ⟶ S'.X₃ => Ev.map f) sp.s_g)).trans
      (Ev.map_id S'.X₃)
  change ∃ s : (S.map (actualAdditive A)).X₃.obj.obj (op V) ⟶
      (S.map (actualAdditive A)).X₂.obj.obj (op V),
    s ≫ (S.map (actualAdditive A)).g.hom.app (op V) =
      𝟙 ((S.map (actualAdditive A)).X₃.obj.obj (op V))
  rw [← hImage]
  -- The two functors agree on this section object and morphism by the
  -- same pointwise restriction and additive forget used in the old proof.
  change ∃ s : Ev.obj S'.X₃ ⟶ Ev.obj S'.X₂,
    s ≫ Ev.map S'.g = 𝟙 (Ev.obj S'.X₃)
  exact ⟨Ev.map sp.s, hh⟩

/-- In particular, any specified section on the same preimage lifts. -/
theorem original_affine_sections_surjective [Smooth p]
    {U : P.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (((oldDirect p i a x J.w).map (actualAdditive A)).g.hom.app
      (op (i ⁻¹ᵁ U))) := by
  let S := (oldDirect p i a x J.w).map (actualAdditive A)
  let V := i ⁻¹ᵁ U
  obtain ⟨s, hs⟩ := original_affine_sections_split p i a x J hU
  intro z
  refine ⟨s z, ?_⟩
  have he := congrArg (fun f : S.X₃.obj.obj (op V) ⟶ S.X₃.obj.obj (op V) => f z) hs
  change S.g.hom.app (op V) (s z) = (𝟙 (S.X₃.obj.obj (op V))) z at he
  exact he.trans (ConcreteCategory.id_apply (X := S.X₃.obj.obj (op V)) z)

end SelectedSameAOldAffineLocalLifts318
