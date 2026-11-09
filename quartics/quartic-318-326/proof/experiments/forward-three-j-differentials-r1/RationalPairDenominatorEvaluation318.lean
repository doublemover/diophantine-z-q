module
public import RationalPairGluing318
public section
noncomputable section
namespace RationalPairDenominatorEvaluation318
open AlgebraicGeometry CategoryTheory Polynomial RationalPairLocalMaps318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluate the whole glued affine morphism through its denominator chart
whenever the actual image of the denominator has a specified inverse. This
is equality of scheme maps over any rational algebra, not merely field points. -/
theorem evaluation_formula (f g : ℚ[X]) (h : IsCoprime f g)
    {A : Type} [CommRing A] [Algebra ℚ A] (φ : ℚ[X] →ₐ[ℚ] A)
    (v : A) (hv : φ g*v=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ RationalPairGluing318.map f g h =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) (φ f*v)).toRingHom) ≫
        JLineAtlas318.chart ℚ 1 := by
  let liftG : DenominatorRing g →ₐ[ℚ] A :=
    IsLocalization.Away.liftAlgHom (f:=φ) g (IsUnit.of_mul_eq_one _ hv)
  have hbase (a : ℚ[X]) : liftG (algebraMap ℚ[X] (DenominatorRing g) a)=φ a := by
    simp only [liftG,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  have hi : liftG (IsLocalization.Away.invSelf g)=v := by
    have he := congrArg liftG (IsLocalization.Away.mul_invSelf (S:=DenominatorRing g) g)
    simp only [map_mul,map_one,hbase] at he
    calc
      _ = (φ g*v)*liftG (IsLocalization.Away.invSelf g) := by rw [hv,one_mul]
      _ = v*(φ g*liftG (IsLocalization.Away.invSelf g)) := by ring
      _ = v := by rw [he,mul_one]
  have hfac : Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom liftG.toRingHom) ≫ denominatorBase g := by
    unfold denominatorBase
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (hbase a).symm
  have heval : liftG.toRingHom.comp
      (Polynomial.aeval (R:=ℚ)
        (algebraMap ℚ[X] (DenominatorRing g) f * IsLocalization.Away.invSelf g)).toRingHom =
      (Polynomial.aeval (R:=ℚ) (φ f*v)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_C,AlgHom.commutes]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        Polynomial.aeval_X,map_mul,hbase,hi]
  rw [hfac,Category.assoc,RationalPairGluing318.denominator_restriction]
  unfold denominatorMap
  rw [←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom (liftG.toRingHom.comp _)) ≫ _ = _
  rw [heval]

end RationalPairDenominatorEvaluation318
