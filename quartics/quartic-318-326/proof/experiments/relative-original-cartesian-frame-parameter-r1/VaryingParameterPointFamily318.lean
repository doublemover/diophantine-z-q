module
public import VaryingParameterPoint318
public section
noncomputable section
namespace VaryingParameterPointFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S)
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
local notation "b" => VaryingWordParameterStructure318.structureMap R A ι
local notation "o" => VaryingWordGlobalOriginalMap318.original R A ι
abbrev family : Scheme := pullback π x.val
abbrev intoFamily : family R A ι S x ⟶ VaryingWordFamilyGluing318.scheme R A ι := pullback.fst π x.val
abbrev projection : family R A ι S x ⟶ Spec (CommRingCat.of S) := pullback.snd π x.val
@[expose] def intoSource : family R A ι S x ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
  (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).lift
    (projection R A ι S x) (intoFamily R A ι S x ≫ o) (by
      rw [Category.assoc,VaryingWordGlobalOriginalMap318.structure_square,
        ← Category.assoc,pullback.condition,Category.assoc,x.property])
@[reassoc] lemma into_projection : intoSource R A ι S x ≫
    VaryingSourceCoefficientPullback318.projection R A S=projection R A ι S x :=
  (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).lift_fst _ _ _
@[reassoc] lemma into_original : intoSource R A ι S x ≫
    VaryingSourceCoefficientPullback318.original R A S=intoFamily R A ι S x ≫ o :=
  (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).lift_snd _ _ _
@[expose] def ambientMap : Spec (CommRingCat.of (S ⊗[R] A)) ⟶ VaryingWordGlobalAmbient318.ambient R A ι :=
  pullback.lift (VaryingSourceCoefficientPullback318.projection R A S ≫ x.val)
    (VaryingSourceCoefficientPullback318.original R A S) (by
      rw [Category.assoc,x.property]
      exact (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).w)
@[reassoc] lemma ambient_projection : ambientMap R A ι S x ≫
    VaryingWordGlobalAmbient318.projection R A ι=VaryingSourceCoefficientPullback318.projection R A S ≫ x.val :=
  pullback.lift_fst _ _ _
@[reassoc] lemma ambient_original : ambientMap R A ι S x ≫ pullback.snd _ _=
    VaryingSourceCoefficientPullback318.original R A S := pullback.lift_snd _ _ _
lemma ambient_cartesian : IsPullback (ambientMap R A ι S x)
    (VaryingSourceCoefficientPullback318.projection R A S)
    (VaryingWordGlobalAmbient318.projection R A ι) x.val := by
  apply IsPullback.of_right (h₁₂ := pullback.snd b (VaryingSourceCoefficientPullback318.base R A)) (h₂₂ := b)
  · simpa only [ambient_original,x.property] using (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).flip
  · exact ambient_projection R A ι S x
  · exact (IsPullback.of_hasPullback b (VaryingSourceCoefficientPullback318.base R A)).flip
lemma source_square : intoFamily R A ι S x ≫ VaryingWordGlobalAmbient318.into R A ι=
    intoSource R A ι S x ≫ ambientMap R A ι S x := by
  apply pullback.hom_ext
  · simp only [Category.assoc,VaryingWordGlobalAmbient318.into_projection,ambient_projection,
      ← Category.assoc,into_projection]
    exact pullback.condition
  · simp only [Category.assoc,VaryingWordGlobalAmbient318.into_original,ambient_original,into_original]
/-- The point fiber is a closed quotient of its ORIGINAL tensor source. -/
lemma source_cartesian : IsPullback (intoFamily R A ι S x) (intoSource R A ι S x)
    (VaryingWordGlobalAmbient318.into R A ι) (ambientMap R A ι S x) := by
  apply IsPullback.of_bot (v₂₁ := VaryingSourceCoefficientPullback318.projection R A S)
    (v₂₂ := VaryingWordGlobalAmbient318.projection R A ι)
  · simpa only [VaryingWordGlobalAmbient318.into_projection,into_projection] using
      IsPullback.of_hasPullback π x.val
  · exact source_square R A ι S x
  · exact ambient_cartesian R A ι S x
instance closed : IsClosedImmersion (intoSource R A ι S x) :=
  MorphismProperty.of_isPullback (source_cartesian R A ι S x) inferInstance
instance finite : IsFinite (projection R A ι S x) := inferInstance
instance flat : Flat (projection R A ι S x) := inferInstance
end VaryingParameterPointFamily318
