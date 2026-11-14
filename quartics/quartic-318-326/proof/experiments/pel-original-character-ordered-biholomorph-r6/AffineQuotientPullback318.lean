module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace AffineQuotientPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {A B : CommRingCat.{u}} (f : A ⟶ B) (I : Ideal A) (J : Ideal B)
  (hJ : J = Ideal.map f.hom I)

lemma ideal_le : I ≤ Ideal.comap f.hom J := by
  rw [hJ]
  exact Ideal.le_comap_map

@[expose] def arrow : CommRingCat.of (A ⧸ I) ⟶ CommRingCat.of (B ⧸ J) :=
  CommRingCat.ofHom (Ideal.quotientMap J f.hom (ideal_le f I J hJ))

lemma square : f ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
    CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ arrow f I J hJ := by
  apply CommRingCat.hom_ext
  exact (Ideal.quotientMap_comp_mk (ideal_le f I J hJ)).symm

/-- The genuine quotient square is a ring pushout, including nonreduced
coefficient rings. No flatness or radical replacement is required. -/
lemma pushout_square : IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (CommRingCat.ofHom (Ideal.Quotient.mk J)) (arrow f I J hJ) := by
  let descend (s : PushoutCocone f (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
      CommRingCat.of (B ⧸ J) ⟶ s.pt := CommRingCat.ofHom (Ideal.Quotient.lift J s.inl.hom (by
        change J ≤ RingHom.ker s.inl.hom
        rw [hJ]
        apply Ideal.map_le_iff_le_comap.mpr
        intro a ha
        change s.inl.hom (f.hom a) = 0
        have he := congrArg (fun k : A ⟶ s.pt => k.hom a) s.condition
        change s.inl.hom (f.hom a) = s.inr.hom (Ideal.Quotient.mk I a) at he
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha,map_zero] at he
        exact he))
  apply IsPushout.of_isColimit
  refine PushoutCocone.IsColimit.mk (square f I J hJ) descend ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    ext b
    rfl
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun k : A ⟶ s.pt => k.hom a) s.condition
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    exact congrArg (fun k : B ⟶ s.pt => k.hom b) hm

lemma pullback_square : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) (Spec.map (arrow f I J hJ))
    (Spec.map f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (pushout_square f I J hJ)

/-- Restriction of the ACTUAL zero quotient along an affine open immersion
is again open, because the preceding square is genuinely Cartesian. -/
instance arrow_open [IsOpenImmersion (Spec.map f)] :
    IsOpenImmersion (Spec.map (arrow f I J hJ)) :=
  MorphismProperty.of_isPullback (pullback_square f I J hJ) inferInstance
end AffineQuotientPullback318
