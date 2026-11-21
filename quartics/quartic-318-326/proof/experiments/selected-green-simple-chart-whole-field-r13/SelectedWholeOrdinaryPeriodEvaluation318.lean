module
public import SelectedActualUnsignedPeriodPoint318
public import SelectedActualSignComplexLift318
public import SelectedActualPeriodFiber318
public import SelectedLiteralOpenJPeriod318
public import SelectedPrimitiveSameRootEvaluation318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open scoped MatrixGroups
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedPrimitiveSameRootEvaluation318 OpenJComplexEvaluation318

namespace SelectedWholeOrdinaryPeriodEvaluation318

variable (N : ℕ) [NeZero N] [IsFinite (kernelProjection N N)]
  [Etale (kernelProjection N N)]
variable (hN : 2 < N) (I : Ideal (D N))
variable (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I)))
variable (hb : primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I))
variable (he : intoAffine N N (by omega : 1 < N) =
  e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
variable (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
variable (hσ : σ.comp (q N I) = (q N I).comp (sign N))
variable (p : (R N)[X]) (ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ)
variable (hep : ep (AdjoinRoot.root p) = coordinate N I σ hσ)

/-- Surjectivity on the entire monogenic ordinary complex chart.
The original relative primitive affine description is explicit; no
modular compact geometry, no choice of component, and no comparison
of independent counts enters the proof. -/
include hN hb he hσ hep in
theorem point_surjective (f : AdjoinRoot p →+* ℂ) :
    ∃ τ : UpperHalfPlane, ∃ h : Admissible τ,
      rootEval N I e hb τ h σ p ep = f := by
  let F := fixed N I σ
  let fF : F →+* ℂ := f.comp ep.symm.toRingHom
  have hY : IsUnit (ybar N I) :=
    SelectedPrimitiveOrdinateUnit318.ordinate_unit N N (by omega) I e he hN
  obtain ⟨g,hg⟩ := SelectedActualSignComplexLift318.lift_exists N I σ hσ hY fF
  let fR : R N →+* ℂ := g.comp (algebraMap (R N) (D N ⧸ I))
  have hbase (r : R N) : fR r = f (algebraMap (R N) (AdjoinRoot p) r) := by
    have h := hg (ep (algebraMap (R N) (AdjoinRoot p) r))
    change g ((ep (algebraMap (R N) (AdjoinRoot p) r) : F) : D N ⧸ I) =
      f (ep.symm (ep (algebraMap (R N) (AdjoinRoot p) r))) at h
    rw [AlgEquiv.symm_apply_apply,AlgEquiv.commutes] at h
    exact h
  have hroot : g (xbar N I) = f (AdjoinRoot.root p) := by
    have h := hg (ep (AdjoinRoot.root p))
    change g ((ep (AdjoinRoot.root p) : F) : D N ⧸ I) =
      f (ep.symm (ep (AdjoinRoot.root p))) at h
    rw [AlgEquiv.symm_apply_apply,hep] at h
    exact h
  obtain ⟨τ,ht,hr⟩ := SelectedLiteralOpenJPeriod318.exists_period_evaluation N fR
  obtain ⟨P,hP,hxP⟩ := SelectedActualUnsignedPeriodPoint318.read_point N (by omega)
    I e hb he τ ht g hr.symm
  obtain ⟨γ,hγ,hj,hx⟩ := SelectedActualPeriodFiber318.every_fiber_mark N τ ht P hP
  have hγR : evaluation N (γ • τ) hγ = fR := by
    apply SelectedLiteralOpenJPeriod318.ringHom_ext
    rw [evaluation_jCoord,hj,← evaluation_jCoord N τ ht,hr]
  refine ⟨γ • τ,hγ,?_⟩
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply,← AdjoinRoot.algebraMap_eq,rootEval_base,hγR,hbase]
  · rw [rootEval_root N I e hb _ hγ σ hσ p ep hep (by omega) he]
    exact hx.trans (hxP.trans hroot)

end SelectedWholeOrdinaryPeriodEvaluation318

#print axioms SelectedWholeOrdinaryPeriodEvaluation318.point_surjective
