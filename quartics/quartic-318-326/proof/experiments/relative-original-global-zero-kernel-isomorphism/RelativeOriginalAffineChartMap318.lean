module
public import RelativeOriginalAffineChart318
public section
noncomputable section
namespace RelativeOriginalAffineChartMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k R B O : CommRingCat.{u}) [Algebra k R] [Algebra k B] [Algebra k O]
  (g : B →ₐ[k] O)

def ringMap : CommRingCat.of (R ⊗[k] B) ⟶ CommRingCat.of (R ⊗[k] O) :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k R) g).toRingHom

def originalB : B ⟶ CommRingCat.of (R ⊗[k] B) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := B)).toRingHom

def originalO : O ⟶ CommRingCat.of (R ⊗[k] O) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := O)).toRingHom

lemma original_square : originalB k R B ≫ ringMap k R B O g =
    CommRingCat.ofHom g.toRingHom ≫ originalO k R O := by
  apply CommRingCat.hom_ext
  ext b
  simp [originalB,originalO,ringMap]

lemma coefficient_square : CommRingCat.ofHom (algebraMap R (R ⊗[k] B)) ≫
    ringMap k R B O g = CommRingCat.ofHom (algebraMap R (R ⊗[k] O)) := by
  apply CommRingCat.hom_ext
  ext r
  simp [ringMap]

lemma spec_original : Spec.map (ringMap k R B O g) ≫ Spec.map (originalB k R B) =
    Spec.map (originalO k R O) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [← Spec.map_comp,← Spec.map_comp,original_square]

lemma spec_coefficient : Spec.map (ringMap k R B O g) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] B))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] O))) := by
  rw [← Spec.map_comp,coefficient_square]

variable {X : Scheme.{u}} (p : X ⟶ Spec k) (jB : Spec B ⟶ X) (jO : Spec O ⟶ X)
  (hB : jB ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (hO : jO ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k O)))

/-- The literal extended original ring map is the actual map between the
WHOLE base-changed chart objects, with both pullback projections retained. -/
lemma into_square (hg : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ jB = jO) :
    Spec.map (ringMap k R B O g) ≫
      RelativeOriginalAffineChart318.into k R B p jB hB =
      RelativeOriginalAffineChart318.into k R O p jO hO := by
  apply pullback.hom_ext
  · rw [Category.assoc,RelativeOriginalAffineChart318.over_original,
      RelativeOriginalAffineChart318.over_original,← Category.assoc,
      spec_original,Category.assoc,hg]
  · rw [Category.assoc,RelativeOriginalAffineChart318.over_test,
      RelativeOriginalAffineChart318.over_test,spec_coefficient]
end RelativeOriginalAffineChartMap318
