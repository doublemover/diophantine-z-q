module

public import SelectedSameAOldAffineLocalLifts318
public import SelectedSameASignedCoverInjectiveJoin318

/-!
# The old affine right inverses supply the same signed-cover lifts

Apply the geometrically split right arrow on each exact preimage open
of the given affine family to the restriction of the specified top
section. The existing signed comparison consumes these very lifts;
there is no second chart, top section, or choice of local preimage.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAOldAffineSignedHandoff318

universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAOldMarkedCompositeZero318
open SelectedSameAOldGlobalExactCotangent318
open SelectedSameAOldAffineLocalLifts318
open SelectedActualAdditiveStalkLocalExact318
open SelectedSameALiteralInjectiveRow318
open SelectedSameASignedLiftCocycle318

variable {k T : Type u} [Field k] [CommRing T] [Algebra k T]
variable {A P : Scheme.{u}}
variable (p : P ⟶ Spec (CommRingCat.of T)) (i : A ⟶ P)
variable (a : A ⟶ Spec (CommRingCat.of k)) (x : T →ₐ[k] k)
variable (J : IsPullback i a p (Spec.map (CommRingCat.ofHom x.toRingHom)))
variable [Smooth p] [HasSheafify
  (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}]

/-- The input family is retained literally, e.g. the affine-basis
preimages used to prove original exactness. The one local right inverse
per open supplies both the lifts and the image-lift comparison. -/
theorem original_affine_cover_coeff {ι : Type u} (U : ι → P.Opens)
    (hU : ∀ j, IsAffineOpen (U j))
    {L : Sheaf (_root_.Opens.grothendieckTopology (A : TopCat.{u})) AddCommGrpCat.{u}} :
    let X := (A : TopCat.{u})
    let S := (oldDirect p i a x J.w).map (actualAdditive A)
    let hOld := original_additive_short_exact p i a x J
    let V : ι → Opens X := fun j => i ⁻¹ᵁ U j
    ∃ s : ∀ j, S.X₃.obj.obj (op (V j)) ⟶ S.X₂.obj.obj (op (V j)),
    ∃ hs : ∀ j, s j ≫ S.g.hom.app (op (V j)) = 𝟙 (S.X₃.obj.obj (op (V j))),
      ∀ (lambdaA : S.X₁ ⟶ L) (z : S.X₃.obj.obj (op (⊤ : Opens X))),
      let t : ∀ j, S.X₂.obj.obj (op (V j)) := fun j => s j (res X S.X₃ le_top z)
      ∃ ht : ∀ j, S.g.hom.app (op (V j)) (t j) = res X S.X₃ le_top z,
        let C := target X L
        let G := factor X hOld lambdaA
        let z' := G.τ₃.hom.app (op (⊤ : Opens X)) z
        let t' := fun j => G.τ₂.hom.app (op (V j)) (t j)
        ∃ hImage : ∀ j, C.g.hom.app (op (V j)) (t' j) = res X C.X₃ le_top z',
          ∀ j j', coeff X C (target_shortExact X L) V z' t' hImage j j' =
            lambdaA.hom.app (op (V j ⊓ V j')) (coeff X S hOld V z t ht j j') := by
  dsimp only
  let X := (A : TopCat.{u})
  let S := (oldDirect p i a x J.w).map (actualAdditive A)
  let V : ι → Opens X := fun j => i ⁻¹ᵁ U j
  have hSplit (j : ι) : ∃ s : S.X₃.obj.obj (op (V j)) ⟶ S.X₂.obj.obj (op (V j)),
      s ≫ S.g.hom.app (op (V j)) = 𝟙 (S.X₃.obj.obj (op (V j))) :=
    original_affine_sections_split p i a x J (hU j)
  let s (j : ι) := Classical.choose (hSplit j)
  have hs (j : ι) : s j ≫ S.g.hom.app (op (V j)) = 𝟙 (S.X₃.obj.obj (op (V j))) :=
    Classical.choose_spec (hSplit j)
  refine ⟨s, hs, ?_⟩
  intro lambdaA z
  let t (j : ι) : S.X₂.obj.obj (op (V j)) := s j (res X S.X₃ le_top z)
  have ht (j : ι) : S.g.hom.app (op (V j)) (t j) = res X S.X₃ le_top z := by
    let b : S.X₃.obj.obj (op (V j)) := res X S.X₃ le_top z
    have e := congrArg (fun f : S.X₃.obj.obj (op (V j)) ⟶ S.X₃.obj.obj (op (V j)) => f b) (hs j)
    change S.g.hom.app (op (V j)) (s j b) = (𝟙 (S.X₃.obj.obj (op (V j)))) b at e
    exact e.trans (ConcreteCategory.id_apply (X := S.X₃.obj.obj (op (V j))) b)
  refine ⟨ht, ?_⟩
  exact SelectedSameASignedCoverInjectiveJoin318.factor_cover_coeff X
    (original_additive_short_exact p i a x J) lambdaA V z t ht

end SelectedSameAOldAffineSignedHandoff318
