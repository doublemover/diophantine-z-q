module
public import PullbackIntersectionBaseChange318
public import OriginalIntegerRationalGlobalRegularity318
public import OriginalIntegerRationalOverlapSquares318
public section
noncomputable section
namespace OriginalIntegerRationalIntersection318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ)
open OriginalIntegerRationalGlobalRegularity318
abbrev O := OriginalIntegerNormalizedOverlap318.Overlap c
abbrev originalOverlapMap := OriginalIntegerNormalizedOverlap318.intoFinite c ≫
  OriginalIntegerClosureGluing318.finiteChart c

private theorem spec_int_comp {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
  rw [← Spec.map_comp]
  exact congrArg (fun g : ℤ →+* B => Spec.map (CommRingCat.ofHom g))
    (Subsingleton.elim (f.comp (algebraMap ℤ A)) (algebraMap ℤ B))

theorem overlap_structure : originalOverlapMap c ≫ integralStructure c =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (O c))) := by
  rw [originalOverlapMap, Category.assoc, finite_structure]
  exact spec_int_comp (OriginalIntegerNormalizedOverlap318.inclusion c).toRingHom

/-- The original integral intersection square, transported through actual
base change, not a claimed equality of carrier sets. -/
@[expose] def changedIntersectionIso :
    PullbackIntersectionBaseChange318.ChangedOriginal
      (OriginalIntegerClosureGluing318.finiteChart c)
      (OriginalIntegerClosureGluing318.infinityChart c)
      (pullback.fst (integralStructure c) baseChangeMap) ≅
    pullback (originalOverlapMap c)
      (pullback.fst (integralStructure c) baseChangeMap) := by
  let H := OriginalIntegerClosureGluing318.intersection_square c
  exact asIso (pullback.map _ _ _ _ H.isoPullback.inv (𝟙 _) (𝟙 _)
    (by simp only [Category.comp_id, originalOverlapMap, ← Category.assoc,
      H.isoPullback_inv_fst]) (by simp))

/-- The actual base change of the original common overlap is canonically
Spec of its integer-only rational tensor ring. -/
@[expose] def overlapFiberIso :
    pullback (originalOverlapMap c)
      (pullback.fst (integralStructure c) baseChangeMap) ≅
    Spec (CommRingCat.of (O c ⊗[ℤ] ℚ)) := by
  refine pullbackRightPullbackFstIso (integralStructure c) baseChangeMap _ ≪≫ ?_
  rw [overlap_structure]
  exact pullbackSpecIso ℤ (O c) ℚ

/-- The FULL categorical intersection of the two actual rational-fiber
cover charts is this literal coefficient-rationalized common overlap.
Projection compatibility is a further explicit obligation, not included
silently in the bare existence of this isomorphism. -/
@[expose] def intersectionIso :
    pullback ((rationalCover c).f false) ((rationalCover c).f true) ≅
      Spec (CommRingCat.of (O c ⊗[ℤ] ℚ)) := by
  change PullbackIntersectionBaseChange318.ChangedIntersection
    (OriginalIntegerClosureGluing318.finiteChart c)
    (OriginalIntegerClosureGluing318.infinityChart c)
    (pullback.fst (integralStructure c) baseChangeMap) ≅ _
  exact PullbackIntersectionBaseChange318.iso _ _ _ ≪≫
    changedIntersectionIso c ≪≫ overlapFiberIso c

end OriginalIntegerRationalIntersection318
