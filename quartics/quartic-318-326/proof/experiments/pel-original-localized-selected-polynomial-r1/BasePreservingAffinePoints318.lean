module
public import AdjoinRootSeparablePointCount318
public section
noncomputable section
namespace BasePreservingAffinePoints318
open Polynomial AlgebraicGeometry CategoryTheory
variable {R L : Type} [CommRing R] [CommRing L]
variable (g : R →+* L) (v : R →+* ℂ)
abbrev Points := {f : L →+* ℂ // f.comp g = v}
abbrev SchemePoints :=
  {q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of L) //
    q ≫ Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom v)}
@[expose] def toScheme (f : Points g v) : SchemePoints g v :=
  ⟨Spec.map (CommRingCat.ofHom f.val),by
    rw [←Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) f.property⟩
theorem toScheme_bijective : Function.Bijective (toScheme g v) := by
  constructor
  · intro f h he
    apply Subtype.ext
    exact congrArg (fun a => a.hom) (Spec.map_injective (congrArg Subtype.val he))
  · rintro ⟨q,hq⟩
    obtain ⟨f,rfl⟩ := Spec.map_surjective q
    have hf : f.hom.comp g = v := by
      rw [←Spec.map_comp] at hq
      exact congrArg (fun a => a.hom) (Spec.map_injective hq)
    exact ⟨⟨f.hom,hf⟩,Subtype.ext rfl⟩
@[expose] def schemeEquiv : Points g v ≃ SchemePoints g v :=
  Equiv.ofBijective (toScheme g v) (toScheme_bijective g v)

/-- Every point of the entire original order, and conversely every
monogenic point, is transported along the ACTUAL coefficient-preserving
ring equivalence. No chosen component or original analytic point enters. -/
@[expose] def monogenicPointsEquiv (Q : Polynomial R) (e : AdjoinRoot Q ≃+* L)
    (he : ∀a, e (AdjoinRoot.of Q a) = g a) :
    Points g v ≃ AdjoinRootSpecializedPoints318.Points Q v where
  toFun f := ⟨f.val.comp e.toRingHom,by
    ext a
    change f.val (e (AdjoinRoot.of Q a)) = v a
    rw [he]
    exact congrArg (fun h : R →+* ℂ => h a) f.property⟩
  invFun f := ⟨f.val.comp e.symm.toRingHom,by
    ext a
    change f.val (e.symm (g a)) = v a
    rw [←he,e.symm_apply_apply]
    exact congrArg (fun h : R →+* ℂ => h a) f.property⟩
  left_inv f := by
    apply Subtype.ext
    ext a
    change f.val (e (e.symm a)) = f.val a
    rw [e.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    ext a
    change f.val (e.symm (e a)) = f.val a
    rw [e.symm_apply_apply]

@[expose] def monogenicSchemeEquiv (Q : Polynomial R) (e : AdjoinRoot Q ≃+* L)
    (he : ∀a, e (AdjoinRoot.of Q a) = g a) :
    SchemePoints g v ≃ AdjoinRootSpecializedPoints318.SchemePoints Q v :=
  (schemeEquiv g v).symm.trans
    ((monogenicPointsEquiv g v Q e he).trans
      (AdjoinRootSpecializedPoints318.schemeEquiv Q v))

theorem point_count (Q : Polynomial R) (e : AdjoinRoot Q ≃+* L)
    (he : ∀a, e (AdjoinRoot.of Q a) = g a) (hm : Q.Monic) (hs : Q.Separable) :
    Nat.card (SchemePoints g v) = Q.natDegree :=
  (Nat.card_congr (monogenicSchemeEquiv g v Q e he)).trans
    (AdjoinRootSeparablePointCount318.point_count Q v hm hs)

/-- Simple roots now belong to the whole ORIGINAL source order, with
its actual regular primitive generator, not merely to an auxiliary order. -/
theorem every_point_simple (Q : Polynomial R) (e : AdjoinRoot Q ≃+* L)
    (he : ∀a, e (AdjoinRoot.of Q a) = g a) (hs : Q.Separable)
    (f : Points g v) :
    (Q.map v).derivative.eval (f.val (e (AdjoinRoot.root Q))) ≠ 0 :=
  AdjoinRootSeparablePointCount318.every_point_simple Q v hs
    (monogenicPointsEquiv g v Q e he f)
end BasePreservingAffinePoints318
