module
public import CanonicalActualDescentFunctor318
public section
noncomputable section
namespace OriginalAffineLineFaithfulness318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  {L K : Line (Spec R)}

/-- Faithfully flat pullback detects maps between arbitrary original affine
lines, not only maps whose source and target are already displayed tilde objects. -/
lemma pullback_map_injective (g h : L.object ⟶ K.object)
    (he : (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map g =
      (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map h) : g = h := by
  let a := OriginalLineAffineModel318.canonicalIso R L
  let b := OriginalLineAffineModel318.canonicalIso R K
  have hn : a.hom ≫ g ≫ b.inv = a.hom ≫ h ≫ b.inv := by
    apply FaithfullyFlatTildeFaithful318.pullback_map_injective R S
    simp only [Functor.map_comp]
    rw [he]
  apply (cancel_epi a.hom).mp
  apply (cancel_mono b.inv).mp
  exact hn

lemma canonical_map_injective : Function.Injective
    (CanonicalActualDescentFunctor318.map R S (L := L) (K := K)) := by
  intro g h he
  exact pullback_map_injective R S g h (congrArg ActualAffineDescentData318.Hom.sheafHom he)

/-- Equality of composites and identity/cocycle equations can be checked
on the original faithfully flat cover of the original affine lines. -/
lemma maps_eq_of_cover_square (g h : L.object ⟶ K.object)
    {N : (Spec S).Modules}
    (e : (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).obj K.object ≅ N)
    (he : (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map g ≫ e.hom =
      (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R S)).map h ≫ e.hom) : g = h :=
  pullback_map_injective R S g h ((cancel_mono e.hom).mp he)
end OriginalAffineLineFaithfulness318
