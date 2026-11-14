module
public import RefinementCanonicalComparison318
public section
noncomputable section
namespace RefinedOriginalLineMapDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentBaseChangeMaps318 OriginalGlobalDescentCategory318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  {L K : Line Y}

@[expose] def refined (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) :
    Hom (OriginalCanonicalDescent318.datum g L) (OriginalCanonicalDescent318.datum g K) :=
  (RefinementCanonicalComparison318.comparison f g a factor).inv.app L ≫
    (RefinementCanonicalComparison318.change f g a factor).map h ≫
      (RefinementCanonicalComparison318.comparison f g a factor).hom.app K

/-- Full map descent between arbitrary original base lines through the
supplied affine faithfully flat refinement. -/
@[expose] def descend (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) : L.object ⟶ K.object :=
  OriginalGlobalLineMapDescent318.descend g (refined f g a factor h)

lemma descend_hom (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) :
    OriginalCanonicalDescent318.map f (descend f g a factor h) = h := by
  let C := RefinementCanonicalComparison318.comparison f g a factor
  let T := RefinementCanonicalComparison318.change f g a factor
  have hd : (canonical g).map (descend f g a factor h) = refined f g a factor h :=
    Hom.ext (OriginalGlobalLineMapDescent318.descend_cover g (refined f g a factor h))
  apply RefinementDescentFaithfulness318.map_injective f g a factor
  change T.map ((canonical f).map (descend f g a factor h)) = T.map h
  apply (cancel_mono (C.hom.app K)).mp
  rw [C.hom.naturality (descend f g a factor h),hd]
  change C.hom.app L ≫ (C.inv.app L ≫ T.map h ≫ C.hom.app K) = T.map h ≫ C.hom.app K
  simp only [Iso.hom_inv_id_app_assoc]

lemma descend_cover (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) :
    (Scheme.Modules.pullback f).map (descend f g a factor h) = h.sheafHom :=
  congrArg Hom.sheafHom (descend_hom f g a factor h)

lemma descend_unique (h : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K)) (k : L.object ⟶ K.object)
    (hk : (Scheme.Modules.pullback f).map k = h.sheafHom) : k = descend f g a factor h :=
  RefinedCoverFaithfulness318.pullback_injective f g a factor k (descend f g a factor h)
    (hk.trans (descend_cover f g a factor h).symm)

@[expose] def homEquiv : Hom (OriginalCanonicalDescent318.datum f L)
    (OriginalCanonicalDescent318.datum f K) ≃ (L.object ⟶ K.object) where
  toFun := descend f g a factor
  invFun := OriginalCanonicalDescent318.map f
  left_inv := descend_hom f g a factor
  right_inv k := (descend_unique f g a factor (OriginalCanonicalDescent318.map f k) k rfl).symm
end RefinedOriginalLineMapDescent318
