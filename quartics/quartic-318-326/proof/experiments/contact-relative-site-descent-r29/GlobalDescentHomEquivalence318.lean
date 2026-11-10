module
public import OriginalGlobalDescentCategory318
public section
noncomputable section
namespace GlobalDescentHomEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
open AffineGlobalMorphismEffectivity318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  {D E : Datum f}

/-- Any original map between reconstructed base lines gives an actual
covering map by the displayed comparison and its compatible inverse. -/
@[expose] def recover (g : (line f D).object ⟶ (line f E).object) : Hom D E :=
  (AffineMorphismGlobalEffectivity318.inverse f D).comp
    ((OriginalCanonicalDescent318.map f g).comp (AffineMorphismGlobalEffectivity318.hom f E))

lemma recover_map (h : Hom D E) : recover f (map f h) = h := by
  apply Hom.ext
  change (comparison f D).inv ≫ (Scheme.Modules.pullback f).map (map f h) ≫
    (comparison f E).hom = h.sheafHom
  rw [AffineGlobalMapCoverSquare318.cover_square,Iso.inv_hom_id_assoc]

lemma map_recover (g : (line f D).object ⟶ (line f E).object) : map f (recover f g) = g := by
  symm
  apply map_unique f (recover f g)
  change (Scheme.Modules.pullback f).map g ≫ (comparison f E).hom =
    (comparison f D).hom ≫ (comparison f D).inv ≫
      (Scheme.Modules.pullback f).map g ≫ (comparison f E).hom
  simp only [Iso.hom_inv_id_assoc]

/-- Full faithfulness of reconstruction on the original descent category,
with original sheaf maps at both ends and the literal covering square. -/
@[expose] def homEquiv : Hom D E ≃ ((line f D).object ⟶ (line f E).object) where
  toFun := map f
  invFun := recover f
  left_inv := recover_map f
  right_inv := map_recover f

lemma map_injective : Function.Injective (map f (D:=D) (E:=E)) := (homEquiv f).injective

/-- Every canonical map between arbitrary original base lines is detected
faithfully, even before the remaining base-side unit is assembled. -/
lemma canonical_map_injective {L K : Line Y} :
    Function.Injective (OriginalCanonicalDescent318.map f (L:=L) (K:=K)) := by
  intro a b h
  exact GlobalAffineLineFaithfulness318.pullback_injective f a b
    (congrArg Hom.sheafHom h)
end GlobalDescentHomEquivalence318
