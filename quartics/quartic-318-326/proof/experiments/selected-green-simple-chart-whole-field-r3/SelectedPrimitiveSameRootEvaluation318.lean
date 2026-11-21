module
public import SelectedActualPrimitiveMark318
public import SelectedPrimitiveXCharacteristic318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedActualPrimitiveMark318 SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open OpenJComplexEvaluation318 CanonicalXModularity318

namespace SelectedPrimitiveSameRootEvaluation318

variable (M : ℕ) [NeZero M]
variable [IsFinite (kernelProjection M M)] [Etale (kernelProjection M M)]
variable (I : Ideal (D M))
variable (e : PrimitiveScheme M M ≅ Spec (CommRingCat.of (D M ⧸ I)))
variable (hb : primitiveProjection M M = e.hom ≫ Spec.algebraMap (R M) (D M ⧸ I))
variable (tau : UpperHalfPlane) (h : Admissible tau)

/-- The unsigned coordinate evaluation comes from the actual Scheme point,
the same affine isomorphism, and the actual period base homomorphism. -/
@[expose] def unsignedEval :
    letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
    (D M ⧸ I) →ₐ[R M] ℂ := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  exact AffineProductEvaluation318.toAlgHom (primitivePoint M tau h ≫ e.hom) (by
    rw [Category.assoc,← hb,primitivePoint_projection] <;> rfl)

theorem unsignedEval_scheme :
    Spec.map (CommRingCat.ofHom (unsignedEval M I e hb tau h).toRingHom) =
      primitivePoint M tau h ≫ e.hom := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  exact AffineProductEvaluation318.map_toAlgHom _ _

/-- The x read from that algebra map is the same normalized holomorphic
period coordinate. This uses the exact finite-chart morphism, not a
record with an independently provided x-value. -/
theorem unsignedEval_x (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    unsignedEval M I e hb tau h (xbar M I) =
      SelectedMarkedPeriodCoordinate318.arithmeticX M tau := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  let v : D M →ₐ[R M] ℂ := (unsignedEval M I e hb tau h).comp (q M I)
  let g : AffineSchemeSolutions318.SchemePoints (K := ℂ) (A M) (B M) :=
    Spec.homEquivAlgHom.symm v
  have hg : CompletedFieldPoints318.finiteInclusion (A M) (B M) g = curvePoint M tau h := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom v.toRingHom) ≫ chart M = (curvePoint M tau h).val
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom (unsignedEval M I e hb tau h).toRingHom) ≫ chart M = _
    rw [Spec.map_comp,unsignedEval_scheme]
    calc
      _ = (primitivePoint M tau h ≫ (e.hom ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫ chart M :=
        congrArg (fun f => f ≫ chart M) (Category.assoc _ _ _)
      _ = _ := by rw [← he,Category.assoc,intoAffine_chart,primitivePoint_curve]
  have hv : CompletedAdditionPoints318.finiteHom M g = v :=
    Spec.homEquivAlgHom.apply_symm_apply v
  have hg' : LiteralCompletedPoints318.fieldPointEquiv M
      (CompletedFieldPoints318.finiteInclusion (A M) (B M) g) =
      (OpenJAnalyticPoints318.pointAddEquiv M tau h).symm
        (MarkedPeriod318.standardPoint M tau) := by
    rw [hg]
    exact (fieldAddEquiv M (K := ℂ)).apply_symm_apply _
  rw [CompletedAdditionPoints318.finite_reading,hv] at hg'
  have hx := congrArg (fun P : (fiber M tau h).toAffine.Point => pointX P) hg'
  change v (SelectedPrimitiveAffineSign318.X M) =
    pointX ((OpenJAnalyticPoints318.pointAddEquiv M tau h).symm
      (MarkedPeriod318.standardPoint M tau)) at hx
  exact hx.trans (SelectedMarkedPeriodCoordinate318.arithmeticX_in_arithmetic_fiber M tau h)

variable (s : (D M ⧸ I) →ₐ[R M] (D M ⧸ I))
variable (hs : s.comp (q M I) = (q M I).comp (sign M))
variable (p : (R M)[X]) (ep : AdjoinRoot p ≃ₐ[R M] fixed M I s)
variable (hep : ep (AdjoinRoot.root p) = coordinate M I s hs)

/-- Actual original point pulled back through the actual root isomorphism.
Its coefficient map may vary with the period, so this is first a ring map
with the base compatibility proved, not one global R-algebra instance on ℂ. -/
@[expose] def rootEval : AdjoinRoot p →+* ℂ := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  exact ((unsignedEval M I e hb tau h).comp
    ((fixed M I s).val.comp ep.toAlgHom)).toRingHom

theorem rootEval_base (r : R M) :
    rootEval M I e hb tau h s p ep (algebraMap (R M) (AdjoinRoot p) r) =
      evaluation M tau h r := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  exact AlgHom.commutes ((unsignedEval M I e hb tau h).comp
    ((fixed M I s).val.comp ep.toAlgHom)) r

include hs hep in
theorem rootEval_root (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    rootEval M I e hb tau h s p ep (AdjoinRoot.root p) =
      SelectedMarkedPeriodCoordinate318.arithmeticX M tau := by
  change unsignedEval M I e hb tau h ((fixed M I s).val (ep (AdjoinRoot.root p))) = _
  rw [hep]
  exact unsignedEval_x M I e hb tau h hM he

/-- On every polynomial representative the genuine algebraic point is
ordinary coefficient evaluation at literal j and the normalized same x. -/
include hs hep in
theorem rootEval_mk (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (f : (R M)[X]) :
    rootEval M I e hb tau h s p ep (AdjoinRoot.mk p f) =
      f.eval₂ (evaluation M tau h) (SelectedMarkedPeriodCoordinate318.arithmeticX M tau) := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  let a := (unsignedEval M I e hb tau h).comp ((fixed M I s).val.comp ep.toAlgHom)
  have ha : a (AdjoinRoot.root p) = SelectedMarkedPeriodCoordinate318.arithmeticX M tau :=
    rootEval_root M I e hb tau h s hs p ep hep hM he
  change a (AdjoinRoot.mk p f) = aeval (SelectedMarkedPeriodCoordinate318.arithmeticX M tau) f
  rw [← AdjoinRoot.aeval_eq,← Polynomial.aeval_algHom_apply,ha]

/-- The actual polynomial relation at the actual chosen period; no
unrelated root or model evaluation is introduced. -/
include hs hep in
theorem period_is_root (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    p.eval₂ (evaluation M tau h) (SelectedMarkedPeriodCoordinate318.arithmeticX M tau) = 0 := by
  rw [← rootEval_mk M I e hb tau h s hs p ep hep hM he,AdjoinRoot.mk_self,map_zero]

/-- The actual evaluated point equals the universal AdjoinRoot lift at
the same analytic x and literal coefficient homomorphism. -/
include hs hep in
theorem rootEval_lift (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    rootEval M I e hb tau h s p ep =
      AdjoinRoot.lift (evaluation M tau h) (SelectedMarkedPeriodCoordinate318.arithmeticX M tau)
        (period_is_root M I e hb tau h s hs p ep hep hM he) := by
  ext a : 1
  obtain ⟨f,rfl⟩ := AdjoinRoot.mk_surjective a
  rw [rootEval_mk M I e hb tau h s hs p ep hep hM he,AdjoinRoot.lift_mk]

end SelectedPrimitiveSameRootEvaluation318

#print axioms SelectedPrimitiveSameRootEvaluation318.unsignedEval_x
#print axioms SelectedPrimitiveSameRootEvaluation318.rootEval_lift
