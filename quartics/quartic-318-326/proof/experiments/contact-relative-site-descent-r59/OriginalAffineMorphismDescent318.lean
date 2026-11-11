module
public import ActualTildeMorphismDescent318
public section
noncomputable section
namespace OriginalAffineMorphismDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDescentData318 ActualAffineDoubleNerve318 CanonicalActualDescentFunctor318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]

/-- The original line's canonical tilde model retains its actual cover and
frames, transported by the actual canonical tilde-Gamma counit. -/
@[expose] def tildeLine (L : Line (Spec R)) : Line (Spec R) where
  object := tilde (OriginalLineAffineModel318.sections R L)
  Index := L.Index
  opens := L.opens
  cover := L.cover
  frame i := L.frame i ≪≫ (Scheme.Modules.restrictFunctor (L.opens i).ι).mapIso
    (OriginalLineAffineModel318.canonicalIso R L).symm

variable {L K : Line (Spec R)}
  (h : Hom (datum R S L) (datum R S K))

/-- Transport a genuine actual-double compatible map through the original
canonical tilde models. Compatibility follows from actual canonical map
naturality and composition, without a new scalar or coalgebra premise. -/
@[expose] def tildeHom :
    Hom (datum R S (tildeLine R L)) (datum R S (tildeLine R K)) :=
  ((map R S (L := tildeLine R L) (K := L)
    (OriginalLineAffineModel318.canonicalIso R L).hom).comp h).comp
      (map R S (L := K) (K := tildeLine R K)
        (OriginalLineAffineModel318.canonicalIso R K).inv)

@[expose] def tildeDatum : ActualTildeMorphismDescent318.Map R S
    (OriginalLineAffineModel318.sections R L) (OriginalLineAffineModel318.sections R K) where
  hom := (tildeHom R S h).sheafHom
  compatible := (tildeHom R S h).commutes

/-- The actual base-line map, ending in the unchanged original sheaves. -/
@[expose] def descend : L.object ⟶ K.object :=
  (OriginalLineAffineModel318.canonicalIso R L).inv ≫
    ActualTildeMorphismDescent318.descend R S (tildeDatum R S h) ≫
      (OriginalLineAffineModel318.canonicalIso R K).hom

lemma descend_cover :
    (Scheme.Modules.pullback (baseMap R S)).map (descend R S h) = h.sheafHom := by
  simp only [descend, Functor.map_comp]
  rw [ActualTildeMorphismDescent318.descend_cover]
  change (Scheme.Modules.pullback (baseMap R S)).map
      (OriginalLineAffineModel318.canonicalIso R L).inv ≫
    ((Scheme.Modules.pullback (baseMap R S)).map (OriginalLineAffineModel318.canonicalIso R L).hom ≫
      h.sheafHom ≫ (Scheme.Modules.pullback (baseMap R S)).map
        (OriginalLineAffineModel318.canonicalIso R K).inv) ≫
      (Scheme.Modules.pullback (baseMap R S)).map (OriginalLineAffineModel318.canonicalIso R K).hom = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp, ← Functor.map_comp, Category.comp_id]

lemma descend_unique (g : L.object ⟶ K.object)
    (hg : (Scheme.Modules.pullback (baseMap R S)).map g = h.sheafHom) : g = descend R S h :=
  OriginalAffineLineFaithfulness318.pullback_map_injective R S g (descend R S h)
    (hg.trans (descend_cover R S h).symm)

/-- Full morphism effectivity between arbitrary original affine lines,
with compatibility on the genuine categorical double and literal pullback. -/
theorem effective : ∃! g : L.object ⟶ K.object,
    (Scheme.Modules.pullback (baseMap R S)).map g = h.sheafHom :=
  ⟨descend R S h, descend_cover R S h, descend_unique R S h⟩

@[expose] def descendedIso (k : Hom (datum R S K) (datum R S L))
    (hk : h.sheafHom ≫ k.sheafHom = 𝟙 _) (kh : k.sheafHom ≫ h.sheafHom = 𝟙 _) :
    L.object ≅ K.object where
  hom := descend R S h
  inv := descend R S k
  hom_inv_id := by
    apply OriginalAffineLineFaithfulness318.pullback_map_injective R S
    rw [Functor.map_comp, descend_cover, descend_cover, Functor.map_id, hk]
  inv_hom_id := by
    apply OriginalAffineLineFaithfulness318.pullback_map_injective R S
    rw [Functor.map_comp, descend_cover, descend_cover, Functor.map_id, kh]
end OriginalAffineMorphismDescent318
