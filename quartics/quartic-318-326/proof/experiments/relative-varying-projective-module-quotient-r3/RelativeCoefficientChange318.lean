module
public import RelativeOriginalAffineChartMap318
public section
noncomputable section
namespace RelativeCoefficientChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k R S B : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k B]
  (f : R →ₐ[k] S)

/-- Change the coefficient factor, leaving the entire original chart ring intact. -/
@[expose] def ringMap : CommRingCat.of (R ⊗[k] B) ⟶ CommRingCat.of (S ⊗[k] B) :=
  CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id k B)).toRingHom

lemma ringMap_tmul (r : R) (b : B) : ringMap k R S B f (r ⊗ₜ[k] b) = f r ⊗ₜ[k] b := by
  simp [ringMap]

lemma original_square : RelativeOriginalAffineChartMap318.originalB k R B ≫
    ringMap k R S B f = RelativeOriginalAffineChartMap318.originalB k S B := by
  apply CommRingCat.hom_ext
  ext b
  simp [RelativeOriginalAffineChartMap318.originalB,ringMap]

lemma coefficient_square : CommRingCat.ofHom (algebraMap R (R ⊗[k] B)) ≫
    ringMap k R S B f = CommRingCat.ofHom f.toRingHom ≫
      CommRingCat.ofHom (algebraMap S (S ⊗[k] B)) := by
  apply CommRingCat.hom_ext
  ext r
  simp [ringMap]

lemma spec_base : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    RelativeOriginalAffineChart318.baseMap k R = RelativeOriginalAffineChart318.baseMap k S := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact f.commutes a

variable {X : Scheme.{u}} (p : X ⟶ Spec k)
/-- Actual p-first coefficient-change map, not a renamed target curve. -/
@[expose] def familyMap : RelativeOriginalAffineChart318.family k S p ⟶
    RelativeOriginalAffineChart318.family k R p :=
  pullback.lift (pullback.fst p (RelativeOriginalAffineChart318.baseMap k S))
    (pullback.snd p (RelativeOriginalAffineChart318.baseMap k S) ≫
      Spec.map (CommRingCat.ofHom f.toRingHom))
    (by rw [Category.assoc,spec_base,pullback.condition])

@[reassoc] lemma familyMap_original : familyMap k R S f p ≫
    pullback.fst p (RelativeOriginalAffineChart318.baseMap k R) =
      pullback.fst p (RelativeOriginalAffineChart318.baseMap k S) := by
  simp only [familyMap,pullback.lift_fst]

@[reassoc] lemma familyMap_test : familyMap k R S f p ≫
    pullback.snd p (RelativeOriginalAffineChart318.baseMap k R) =
      pullback.snd p (RelativeOriginalAffineChart318.baseMap k S) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  simp only [familyMap,pullback.lift_snd]

variable (j : Spec B ⟶ X)
  (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
/-- Both projections identify the literal tensor-factor map with the actual
full chart map over the original coefficient-change map. -/
@[reassoc] lemma into_square : Spec.map (ringMap k R S B f) ≫
    RelativeOriginalAffineChart318.into k R B p j hj =
      RelativeOriginalAffineChart318.into k S B p j hj ≫ familyMap k R S f p := by
  have ho : Spec.map (ringMap k R S B f) ≫
      Spec.map (RelativeOriginalAffineChartMap318.originalB k R B) ≫ j=
        Spec.map (RelativeOriginalAffineChartMap318.originalB k S B) ≫ j := by
    rw [← Spec.map_comp_assoc,original_square]
  have hc : Spec.map (ringMap k R S B f) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] B)))=
        Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[k] B))) ≫
          Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [← Spec.map_comp,coefficient_square,Spec.map_comp]
  have hs := congrArg (fun k => k ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
    (RelativeOriginalAffineChart318.over_test k S B p j hj)
  apply pullback.hom_ext
  · simpa only [Category.assoc,RelativeOriginalAffineChart318.over_original,familyMap_original] using ho
  · simpa only [Category.assoc,RelativeOriginalAffineChart318.over_test,familyMap_test] using
      hc.trans hs.symm

/-- The two independent tensor factors commute. This retains the original
finite/infinity restriction arrows under every coefficient change. -/
lemma edge_square (O : CommRingCat.{u}) [Algebra k O] (g : B →ₐ[k] O) :
    RelativeOriginalAffineChartMap318.ringMap k R B O g ≫ ringMap k R S O f =
      ringMap k R S B f ≫ RelativeOriginalAffineChartMap318.ringMap k S B O g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul r b => simp [ringMap,RelativeOriginalAffineChartMap318.ringMap]
  | add x y hx hy => simp only [map_add,hx,hy]
end RelativeCoefficientChange318
