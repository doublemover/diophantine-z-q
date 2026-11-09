module
public import RationalPairGluing318
public section
noncomputable section
namespace RationalPairNumeratorEvaluation318
open AlgebraicGeometry CategoryTheory Polynomial RationalPairLocalMaps318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate the whole glued affine morphism through its numerator chart
whenever the actual image of the numerator has a specified inverse. This
is equality of scheme maps over any rational algebra, not merely field points. -/
theorem evaluation_formula (f g : ℚ[X]) (h : IsCoprime f g)
    {A : Type} [CommRing A] [Algebra ℚ A] (φ : ℚ[X] →ₐ[ℚ] A)
    (v : A) (hv : φ f*v=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ RationalPairGluing318.map f g h =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (φ g*v)).toRingHom) ≫
        JLineAtlas318.chart ℚ 0 := by
  let liftF : NumeratorRing f →ₐ[ℚ] A :=
    IsLocalization.Away.liftAlgHom (f:=φ) f (IsUnit.of_mul_eq_one _ hv)
  have hbase (a : ℚ[X]) : liftF (algebraMap ℚ[X] (NumeratorRing f) a)=φ a := by
    simp only [liftF,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
  have hi : liftF (IsLocalization.Away.invSelf f)=v := by
    have he := congrArg liftF (IsLocalization.Away.mul_invSelf (S:=NumeratorRing f) f)
    simp only [map_mul,map_one,hbase] at he
    calc
      _ = (φ f*v)*liftF (IsLocalization.Away.invSelf f) := by rw [hv,one_mul]
      _ = v*(φ f*liftF (IsLocalization.Away.invSelf f)) := by ring
      _ = v := by rw [he,mul_one]
  have hfac : Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom liftF.toRingHom) ≫ numeratorBase f := by
    unfold numeratorBase
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (hbase a).symm
  have heval : liftF.toRingHom.comp
      (Polynomial.aeval (R:=ℚ)
        (algebraMap ℚ[X] (NumeratorRing f) g * IsLocalization.Away.invSelf f)).toRingHom =
      (Polynomial.aeval (R:=ℚ) (φ g*v)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_C,AlgHom.commutes]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_X,map_mul,hbase,hi]
  rw [hfac,Category.assoc,RationalPairGluing318.numerator_restriction]
  unfold numeratorMap
  rw [←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom (liftF.toRingHom.comp
    (Polynomial.aeval (R:=ℚ)
      (algebraMap ℚ[X] (NumeratorRing f) g * IsLocalization.Away.invSelf f)).toRingHom)) ≫
        JLineAtlas318.chart ℚ 0 =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (φ g*v)).toRingHom) ≫
      JLineAtlas318.chart ℚ 0
  rw [heval]

end RationalPairNumeratorEvaluation318
