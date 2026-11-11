module
public import ThreeRationalModuliEquiv318
public import ActualThreeModuliSchemeComparison318
public section
noncomputable section
namespace ThreeRationalModuliScheme318
open AlgebraicGeometry CategoryTheory
open ThreeJModuliScheme318 ThreeRationalModuliEquiv318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Generic Spec functor identity before specialization to the large
original localized/tensor carriers. No concrete carrier is unfolded. -/
private lemma spec_iso_factor {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : T →+* R) :
    (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom f)=Spec.map (CommRingCat.ofHom (e.toRingHom.comp f)) := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom f)=_
  rw [←Spec.map_comp]
  rfl

abbrev RationalTarget := Spec (CommRingCat.of ThreeRationalFixed318.Ring)
/-- The original arithmetic quotient after actual rational tensor base
change is isomorphic to the constructed original parameter open. -/
@[expose] def schemeIso : ThreeJModuliScheme318.Source ≅ RationalTarget :=
  Scheme.Spec.mapIso equivalence.toRingEquiv.toCommRingCatIso.op
@[expose] def rationalization : RationalTarget ⟶ ThreeJModuliScheme318.Target :=
  Spec.map (CommRingCat.ofHom ThreeRationalFixed318.includeFixed.toRingHom)

/-- The newly proved isomorphism factors the preceding actual arithmetic
scheme map. Thus it preserves the original fixed algebra and not just j. -/
theorem arithmeticMap_factor : schemeIso.hom ≫ rationalization=arithmeticMap := by
  have he : equivalence.toRingHom.comp ThreeRationalFixed318.includeFixed.toRingHom=
      ThreeJArithmeticAlgebraMap318.fixedMap := RingHom.ext equivalence_fixed
  rw [schemeIso,rationalization,spec_iso_factor,he]
  rfl

/-- An open immersion of the actual rational arithmetic fixed-algebra
scheme into the original projective parameter scheme. -/
@[expose] def rationalEmbedding : RationalTarget ⟶ ProjectiveJLine318.scheme ℚ :=
  schemeIso.inv ≫ ThreeJModuliScheme318.embedding
instance rationalEmbedding_open : IsOpenImmersion rationalEmbedding := by
  unfold rationalEmbedding
  infer_instance
lemma original_embedding_factor : schemeIso.hom ≫ rationalEmbedding=
    ThreeJModuliScheme318.embedding := by
  simp only [rationalEmbedding,←Category.assoc,Iso.hom_inv_id,Category.id_comp]

/-- The original finite global j morphism restricts along the actual
arithmetic open immersion to precisely the previously constructed j map. -/
theorem rational_global_j_square : rationalEmbedding ≫ ThreeProjectiveJMap318.map=
    schemeIso.inv ≫ ThreeJModuliScheme318.rationalJ ≫ JLineAtlas318.chart ℚ 1 := by
  rw [rationalEmbedding,Category.assoc,ThreeJModuliScheme318.global_j_square]

/-- The old actual Γ1(3) comparison lifts through the proved rational
scheme isomorphism, and then returns to the exact original integral point. -/
theorem sourcePoint_arithmetic (q : ThreeArithmeticQuotient318.Source) :
    ActualThreeModuliSchemeComparison318.sourcePoint q ≫ schemeIso.hom ≫ rationalization=
      ThreeArithmeticQuotient318.schemePoint 3 q := by
  rw [arithmeticMap_factor,ActualThreeModuliSchemeComparison318.sourcePoint_arithmetic]

/-- The same lifted point embeds into the projective source as the original
compact analytic/algebraic comparison, with no coordinate relabeling. -/
theorem sourcePoint_compact (q : ThreeArithmeticQuotient318.Source) :
    ActualThreeModuliSchemeComparison318.sourcePoint q ≫ schemeIso.hom ≫ rationalEmbedding=
      (ActualThreeProjectivePoints318.compactPointHomeomorph
        (ActualThreeCuspFilling318.original q.val)).val := by
  rw [original_embedding_factor,ActualThreeModuliSchemeComparison318.sourcePoint_compact]

end ThreeRationalModuliScheme318
