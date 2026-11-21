module
public import SelectedPrimitiveAffineSign318
public import SelectedMarkedPeriodCoordinate318
public import CompletedAdditionPoints318
import all LiteralSchemePointGroup318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open LiteralSchemePointOperations318 OpenJComplexEvaluation318
open scoped Classical

namespace SelectedActualPrimitiveMark318

/-- The genuine field-valued points identify additively with the points of
the literal evaluated short model, by the actual Scheme addition theorem. -/
@[expose] def fieldAddEquiv (M : ℕ) {K : Type} [Field K] [Algebra (R M) K] :
    Points M (Spec.algebraMap (R M) K) ≃+
      (LiteralWeierstrassPoints318.model (K := K) M).Point where
  toEquiv := LiteralCompletedPoints318.fieldPointEquiv M
  map_add' := fun p q => CompletedAdditionPoints318.actual_add M p q

private def baseChangePoints (M : ℕ) {T : Scheme} {b c : T ⟶ Base M}
    (h : b = c) : Points M b ≃+ Points M c := by
  subst c
  exact AddEquiv.refl _

private theorem baseChangePoints_val (M : ℕ) {T : Scheme} {b c : T ⟶ Base M}
    (h : b = c) (p : Points M b) : (baseChangePoints M h p).val = p.val := by
  subst c
  rfl

variable (M : ℕ) [NeZero M] (tau : UpperHalfPlane) (h : Admissible tau)

abbrev complexSpec := Spec (CommRingCat.of ℂ)
abbrev basePoint : complexSpec ⟶ Base M := Spec.map (CommRingCat.ofHom (evaluation M tau h))

/-- The same actual primitive 1/M period after the checked scaling,
now as a Scheme-valued point of the proper arithmetic short model. -/
@[expose] def curvePoint : Points M (basePoint M tau h) := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  exact (fieldAddEquiv M (K := ℂ)).symm
    ((OpenJAnalyticPoints318.pointAddEquiv M tau h).symm (MarkedPeriod318.standardPoint M tau))

theorem curvePoint_order : addOrderOf (curvePoint M tau h) = M := by
  letI : Algebra (R M) ℂ := (evaluation M tau h).toAlgebra
  let e := (fieldAddEquiv M (K := ℂ)).symm
  let f := (OpenJAnalyticPoints318.pointAddEquiv M tau h).symm
  change addOrderOf (e (f (MarkedPeriod318.standardPoint M tau))) = M
  calc
    _ = addOrderOf (f (MarkedPeriod318.standardPoint M tau)) :=
      addOrderOf_injective e.toAddMonoidHom e.injective _
    _ = addOrderOf (MarkedPeriod318.standardPoint M tau) :=
      addOrderOf_injective f.toAddMonoidHom f.injective _
    _ = M := MarkedPeriod318.standardPoint_order M tau

/-- The exact order supplies the actual pullback equation for the kernel,
not a hand-chosen elliptic point with the same x-value. -/
@[expose] def kernelPoint : complexSpec ⟶ Kernel M M :=
  pullback.lift (curvePoint M tau h).val (basePoint M tau h) (by
    have hz : M • curvePoint M tau h = 0 := by
      simpa only [curvePoint_order] using addOrderOf_nsmul_eq_zero (curvePoint M tau h)
    rw [← mul_value]
    exact congrArg Subtype.val hz)

@[reassoc] theorem kernelPoint_inclusion :
    kernelPoint M tau h ≫ inclusion M M = (curvePoint M tau h).val := by
  simp [kernelPoint]

@[reassoc] theorem kernelPoint_projection :
    kernelPoint M tau h ≫ kernelProjection M M = basePoint M tau h := by
  simp [kernelPoint]

theorem kernelPoint_order : addOrderOf (pointOf M M (kernelPoint M tau h)) = M := by
  let e := baseChangePoints M (kernelPoint_projection M tau h)
  have he : e (pointOf M M (kernelPoint M tau h)) = curvePoint M tau h := by
    apply Subtype.ext
    rw [baseChangePoints_val]
    exact kernelPoint_inclusion M tau h
  calc
    _ = addOrderOf (e.toAddMonoidHom (pointOf M M (kernelPoint M tau h))) :=
      (addOrderOf_injective e.toAddMonoidHom e.injective _).symm
    _ = addOrderOf (curvePoint M tau h) :=
      congrArg addOrderOf (show e.toAddMonoidHom
        (pointOf M M (kernelPoint M tau h)) = curvePoint M tau h from he)
    _ = M := curvePoint_order M tau h

variable [IsFinite (kernelProjection M M)] [Etale (kernelProjection M M)]

/-- The same point factors through the actual primitive open, with all
lower-order loci excluded by the already proved additive exact order. -/
@[expose] def primitivePoint : complexSpec ⟶ PrimitiveScheme M M :=
  IsOpenImmersion.lift (inclusionOpen M M) (kernelPoint M tau h) (by
    have hp := (primitive_iff_order M M (kernelPoint M tau h) default
      (Nat.pos_of_ne_zero (NeZero.ne M))).mpr (kernelPoint_order M tau h)
    have hp' : kernelPoint M tau h default ∈ Set.range (inclusionOpen M M) := by
      change kernelPoint M tau h default ∈ Set.range (primitive M M).ι
      rw [Scheme.Opens.range_ι]
      exact hp
    rintro _ ⟨z,rfl⟩
    exact Subsingleton.elim default z ▸ hp')

@[reassoc] theorem primitivePoint_inclusion :
    primitivePoint M tau h ≫ inclusionOpen M M = kernelPoint M tau h :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem primitivePoint_projection :
    primitivePoint M tau h ≫ primitiveProjection M M = basePoint M tau h := by
  rw [← Category.assoc,primitivePoint_inclusion,kernelPoint_projection]

@[reassoc] theorem primitivePoint_curve :
    primitivePoint M tau h ≫ intoCurve M M = (curvePoint M tau h).val := by
  rw [← Category.assoc,primitivePoint_inclusion,kernelPoint_inclusion]

end SelectedActualPrimitiveMark318

#print axioms SelectedActualPrimitiveMark318.curvePoint_order
#print axioms SelectedActualPrimitiveMark318.primitivePoint_projection
