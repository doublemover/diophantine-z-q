module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

@[expose] public section
noncomputable section

namespace OriginalSameJActualDiagonalOpen318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Algebra.TensorProduct
open scoped TensorProduct
universe u

variable {U C S : Scheme.{u}} (i : U ⟶ C) (f : C ⟶ S)

abbrev productMap : pullback (i ≫ f) (i ≫ f) ⟶ pullback f f :=
  pullback.map (i ≫ f) (i ≫ f) f f i i (𝟙 S) (Category.comp_id _) (Category.comp_id _)

/-- The whole diagonal over U is the pullback of the whole diagonal of C
to U ×_S U, not just a comparison of their geometric points. -/
theorem restricted_diagonal [Mono i] :
    IsPullback (pullback.diagonal (i ≫ f)) i (productMap i f) (pullback.diagonal f) := by
  let t : U ⟶ pullback (i ≫ f) (i ≫ f) := pullback.diagonal (i ≫ f)
  let e : pullback (i ≫ f) (i ≫ f) ⟶ pullback f f := productMap i f
  let d : C ⟶ pullback f f := pullback.diagonal f
  have w : t ≫ e = i ≫ d := (pullback.comp_diagonal i f).symm
  have left_eq (s : PullbackCone e d) :
      (s.fst ≫ pullback.fst (i ≫ f) (i ≫ f)) ≫ i = s.snd := by
    have h := congrArg (fun v : s.pt ⟶ pullback f f => v ≫ pullback.fst f f) s.condition
    simpa only [Category.assoc, e, productMap, d, pullback.lift_fst,
      pullback.diagonal_fst, Category.comp_id] using h
  have right_eq (s : PullbackCone e d) :
      (s.fst ≫ pullback.snd (i ≫ f) (i ≫ f)) ≫ i = s.snd := by
    have h := congrArg (fun v : s.pt ⟶ pullback f f => v ≫ pullback.snd f f) s.condition
    simpa only [Category.assoc, e, productMap, d, pullback.lift_snd,
      pullback.diagonal_snd, Category.comp_id] using h
  have over_eq (s : PullbackCone e d) :
      s.fst ≫ pullback.fst (i ≫ f) (i ≫ f) =
        s.fst ≫ pullback.snd (i ≫ f) (i ≫ f) :=
    (cancel_mono i).mp ((left_eq s).trans (right_eq s).symm)
  change IsPullback t i e d
  refine IsPullback.of_isLimit' ⟨w⟩
    (PullbackCone.IsLimit.mk w (fun s => s.fst ≫ pullback.fst _ _) ?_ left_eq ?_)
  · intro s
    apply pullback.hom_ext
    · simp only [t,Category.assoc,pullback.diagonal_fst,Category.comp_id]
    · simpa only [t,Category.assoc,pullback.diagonal_snd,Category.comp_id] using over_eq s
  · intro s m hm _
    have h := congrArg
      (fun v : s.pt ⟶ pullback (i ≫ f) (i ≫ f) => v ≫ pullback.fst _ _) hm
    simpa only [t,Category.assoc,pullback.diagonal_fst,Category.comp_id] using h

section Affine
variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
variable {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))
variable (j : Spec (CommRingCat.of A) ⟶ C) [IsOpenImmersion j]
variable (base_read : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))

abbrev scalarMap := Spec.map (CommRingCat.ofHom (algebraMap k A))

abbrev affineProductMap :
    pullback (scalarMap k A) (scalarMap k A) ⟶ pullback f f :=
  pullback.map (scalarMap k A) (scalarMap k A) f f j j (𝟙 _)
    ((Category.comp_id _).trans base_read.symm)
    ((Category.comp_id _).trans base_read.symm)

abbrev affineProductOpen : Spec (CommRingCat.of (A ⊗[k] A)) ⟶ pullback f f :=
  (pullbackSpecIso k A A).inv ≫ affineProductMap k A f j base_read

theorem product_is_open : IsOpenImmersion (affineProductOpen k A f j base_read) := by
  letI : IsOpenImmersion (affineProductMap k A f j base_read) := by
    unfold affineProductMap
    infer_instance
  exact IsOpenImmersion.comp _ _

abbrev affineDiagonal : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (A ⊗[k] A)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A).toRingHom)

/-- Real affine tensor-product coordinates on the restriction of the global
diagonal. Both sides use full Spec maps, so arbitrary test algebras work. -/
theorem product_diagonal :
    IsPullback (affineDiagonal k A) j (affineProductOpen k A f j base_read) (pullback.diagonal f) := by
  have h : IsPullback (pullback.diagonal (scalarMap k A)) j
      (affineProductMap k A f j base_read) (pullback.diagonal f) := by
    have s := restricted_diagonal j f
    simpa only [productMap, affineProductMap, scalarMap, base_read] using s
  apply h.of_iso (Iso.refl _) (pullbackSpecIso k A A) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom,Category.id_comp,affineDiagonal,scalarMap,
      diagonal_SpecMap,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  · simp
  · simp only [Iso.refl_hom,affineProductOpen,Category.assoc,Iso.hom_inv_id_assoc,
      Category.comp_id]
  · simp

end Affine
end OriginalSameJActualDiagonalOpen318

#print axioms OriginalSameJActualDiagonalOpen318.restricted_diagonal
#print axioms OriginalSameJActualDiagonalOpen318.product_is_open
#print axioms OriginalSameJActualDiagonalOpen318.product_diagonal
