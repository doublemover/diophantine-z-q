module
public import OriginalIntegerRationalIntersection318
public import IntegerRationalTensorHomExt318
public section
noncomputable section
namespace OriginalIntegerRationalIntersectionProjections318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open OriginalIntegerRationalGlobalRegularity318
open OriginalIntegerRationalIntersection318
variable (c : Fin 4 → ℚˣ)

@[expose] def finiteIso : (rationalCover c).X false ≅
    Spec (CommRingCat.of (FiniteRing c ⊗[ℤ] ℚ)) :=
  IntegerChartBaseChangeIso318.iso (integralStructure c)
    (OriginalIntegerClosureGluing318.finiteChart c) (finite_structure c)

@[expose] def infinityIso : (rationalCover c).X true ≅
    Spec (CommRingCat.of (ReciprocalRing c ⊗[ℤ] ℚ)) :=
  IntegerChartBaseChangeIso318.iso (integralStructure c)
    (OriginalIntegerClosureGluing318.infinityChart c) (reciprocal_structure c)

/-- The same full intersection identification, now choosing a canonical
projection-friendly final tensor isomorphism. -/
@[expose] def iso :
    pullback ((rationalCover c).f false) ((rationalCover c).f true) ≅
      Spec (CommRingCat.of (O c ⊗[ℤ] ℚ)) :=
  PullbackIntersectionBaseChange318.iso _ _ _ ≪≫ changedIntersectionIso c ≪≫
    IntegerChartBaseChangeIso318.iso (integralStructure c)
      (originalOverlapMap c) (overlap_structure c)

private theorem original_left : (iso c).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (O c) (O c ⊗[ℤ] ℚ))) ≫
      OriginalIntegerNormalizedOverlap318.intoFinite c =
    pullback.fst ((rationalCover c).f false) ((rationalCover c).f true) ≫
      pullback.fst (OriginalIntegerClosureGluing318.finiteChart c)
        (pullback.fst (integralStructure c) baseChangeMap) := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    IntegerChartBaseChangeIso318.hom_original_assoc, changedIntersectionIso,
    asIso_hom, pullback.map_fst_assoc,
    (OriginalIntegerClosureGluing318.intersection_square c).isoPullback_inv_fst,
    PullbackIntersectionBaseChange318.iso, PullbackIntersectionBaseChange318.forward,
    pullback.lift_fst_assoc, pullback.lift_fst,
    PullbackIntersectionBaseChange318.leftLeg]

private theorem original_right : (iso c).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (O c) (O c ⊗[ℤ] ℚ))) ≫
      OriginalIntegerReciprocalNormalization318.intoInfinity c =
    pullback.snd ((rationalCover c).f false) ((rationalCover c).f true) ≫
      pullback.fst (OriginalIntegerClosureGluing318.infinityChart c)
        (pullback.fst (integralStructure c) baseChangeMap) := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    IntegerChartBaseChangeIso318.hom_original_assoc, changedIntersectionIso,
    asIso_hom, pullback.map_fst_assoc,
    (OriginalIntegerClosureGluing318.intersection_square c).isoPullback_inv_snd,
    PullbackIntersectionBaseChange318.iso, PullbackIntersectionBaseChange318.forward,
    pullback.lift_fst_assoc, pullback.lift_snd,
    PullbackIntersectionBaseChange318.rightLeg]

private theorem rational_left : (iso c).hom ≫
    Spec.map (CommRingCat.ofHom
      (IntegerRationalTensorNaturality318.rationalCoefficient (O c))) =
    pullback.fst ((rationalCover c).f false) ((rationalCover c).f true) ≫
      (rationalCover c).f false ≫ pullback.snd (integralStructure c) baseChangeMap := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    IntegerChartBaseChangeIso318.hom_rational, changedIntersectionIso,
    asIso_hom, pullback.map_snd_assoc, Category.id_comp,
    PullbackIntersectionBaseChange318.iso, PullbackIntersectionBaseChange318.forward,
    pullback.lift_snd_assoc, PullbackIntersectionBaseChange318.baseLeg]

/-- Both arrows of the FULL categorical intersection are the previously
proved literal rationalized inclusion arrows; this is not just an object iso. -/
theorem finite_projection : (iso c).hom ≫
    Spec.map (CommRingCat.ofHom (OriginalIntegerRationalOverlapSquares318.fromFinite c)) =
    pullback.fst ((rationalCover c).f false) ((rationalCover c).f true) ≫
      (finiteIso c).hom := by
  apply IntegerRationalTensorHomExt318.hom_ext
  · rw [Category.assoc, ← Spec.map_comp]
    change (iso c).hom ≫ Spec.map (CommRingCat.ofHom
      ((OriginalIntegerRationalOverlapSquares318.fromFinite c).comp
        (algebraMap (FiniteRing c) (FiniteRing c ⊗[ℤ] ℚ)))) = _
    rw [OriginalIntegerRationalOverlapSquares318.fromFinite,
      IntegerRationalTensorNaturality318.base_square]
    rw [Spec.map_comp, Category.assoc, original_left]
    simpa only [Category.assoc, finiteIso,
      IntegerChartBaseChangeIso318.hom_original]
  · rw [Category.assoc, ← Spec.map_comp]
    change (iso c).hom ≫ Spec.map (CommRingCat.ofHom
      ((OriginalIntegerRationalOverlapSquares318.fromFinite c).comp
        (IntegerRationalTensorNaturality318.rationalCoefficient (FiniteRing c)))) = _
    rw [OriginalIntegerRationalOverlapSquares318.fromFinite,
      IntegerRationalTensorNaturality318.rational_square, rational_left]
    simp only [Category.assoc, finiteIso, IntegerChartBaseChangeIso318.hom_rational]

theorem infinity_projection : (iso c).hom ≫
    Spec.map (CommRingCat.ofHom (OriginalIntegerRationalOverlapSquares318.fromInfinity c)) =
    pullback.snd ((rationalCover c).f false) ((rationalCover c).f true) ≫
      (infinityIso c).hom := by
  apply IntegerRationalTensorHomExt318.hom_ext
  · rw [Category.assoc, ← Spec.map_comp]
    change (iso c).hom ≫ Spec.map (CommRingCat.ofHom
      ((OriginalIntegerRationalOverlapSquares318.fromInfinity c).comp
        (algebraMap (ReciprocalRing c) (ReciprocalRing c ⊗[ℤ] ℚ)))) = _
    rw [OriginalIntegerRationalOverlapSquares318.fromInfinity,
      IntegerRationalTensorNaturality318.base_square]
    rw [Spec.map_comp, Category.assoc, original_right]
    simpa only [Category.assoc, infinityIso,
      IntegerChartBaseChangeIso318.hom_original]
  · rw [Category.assoc, ← Spec.map_comp]
    change (iso c).hom ≫ Spec.map (CommRingCat.ofHom
      ((OriginalIntegerRationalOverlapSquares318.fromInfinity c).comp
        (IntegerRationalTensorNaturality318.rationalCoefficient (ReciprocalRing c)))) = _
    rw [OriginalIntegerRationalOverlapSquares318.fromInfinity,
      IntegerRationalTensorNaturality318.rational_square, rational_left]
    simp only [Category.assoc, infinityIso, IntegerChartBaseChangeIso318.hom_rational]
    exact congrArg (fun f => f ≫ pullback.snd (integralStructure c) baseChangeMap)
      (pullback.condition (f := (rationalCover c).f false) (g := (rationalCover c).f true))

end OriginalIntegerRationalIntersectionProjections318
