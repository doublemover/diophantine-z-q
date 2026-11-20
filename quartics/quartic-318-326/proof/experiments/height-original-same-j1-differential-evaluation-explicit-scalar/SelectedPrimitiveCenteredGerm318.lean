module
public import SelectedPrimitiveSameRootEvaluation318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Topology TensorProduct
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedPrimitiveSameRootEvaluation318 OpenJComplexEvaluation318

namespace SelectedPrimitiveCenteredGerm318

private theorem eval_analyticAt {A : Type*} [CommRing A]
    (r : ℂ → A →+* ℂ) (x : ℂ → ℂ) (c : ℂ)
    (hr : ∀ a, AnalyticAt ℂ (fun z => r z a) c) (hx : AnalyticAt ℂ x c)
    (f : A[X]) : AnalyticAt ℂ (fun z => f.eval₂ (r z) (x z)) c := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [eval₂_add] using hf.add hg
  | monomial k a => simpa only [eval₂_monomial] using (hr a).mul (hx.pow k)

variable (M : ℕ) [NeZero M]

private theorem eval_polynomial (t : UpperHalfPlane) (ht : Admissible t) (a : ℤ[X]) :
    evaluation M t ht (algebraMap (ℤ[X]) (R M) a) = polynomialEval t a :=
  IsLocalization.Away.lift_eq _ _ _

/-- Regular coefficients in the actual localization are holomorphic
where the genuine branch has j = 1+z. The denominator is the literal
polynomial (6M) j(j−1728), already a unit at the point. -/
theorem coefficient_analyticAt (t : ℂ → UpperHalfPlane) (ht : ∀ z, Admissible (t z))
    (c : ℂ) (hj : ∀ᶠ z in 𝓝 c, ActualQJ318.jInvariant (t z) = 1+z)
    (a : R M) :
    AnalyticAt ℂ (fun z => evaluation M (t z) (ht z) a) c := by
  have hp (f : ℤ[X]) : AnalyticAt ℂ (fun z => polynomialEval (t z) f) c := by
    have h₁ : AnalyticAt ℂ (fun z : ℂ => 1+z) c := analyticAt_const.add analyticAt_id
    apply (eval_analyticAt (fun _ => Int.castRingHom ℂ) _ c
      (fun _ => analyticAt_const) h₁ f).congr
    filter_upwards [hj] with z hz
    change f.eval₂ (Int.castRingHom ℂ) (1+z) =
      f.eval₂ (Int.castRingHom ℂ) (ActualQJ318.jInvariant (t z))
    rw [hz]
  obtain ⟨k,f,hf⟩ := IsLocalization.Away.surj (OpenJModel318.denominator M) a
  have hden (z : ℂ) : polynomialEval (t z) (OpenJModel318.denominator M) ≠ 0 :=
    (denominator_isUnit M (t z) (ht z)).ne_zero
  apply ((hp f).div ((hp (OpenJModel318.denominator M)).pow k)
    (pow_ne_zero k (hden c))).congr
  apply Filter.Eventually.of_forall
  intro z
  have he := congrArg (evaluation M (t z) (ht z)) hf
  rw [map_mul,map_pow,eval_polynomial,eval_polynomial] at he
  exact ((eq_div_iff (pow_ne_zero k (hden z))).mpr he).symm

variable [IsFinite (kernelProjection M M)] [Etale (kernelProjection M M)]
variable (I : Ideal (D M))
variable (e : PrimitiveScheme M M ≅ Spec (CommRingCat.of (D M ⧸ I)))
variable (hb : primitiveProjection M M = e.hom ≫ Spec.algebraMap (R M) (D M ⧸ I))
variable (s : (D M ⧸ I) →ₐ[R M] (D M ⧸ I))
variable (hs : s.comp (q M I) = (q M I).comp (sign M))
variable (p : (R M)[X]) (ep : AdjoinRoot p ≃ₐ[R M] fixed M I s)
variable (hep : ep (AdjoinRoot.root p) = coordinate M I s hs)

include hs hep in
/-- The genuine same-root evaluation of every regular function is
holomorphic in the inverse j germ. F is the ordinary holomorphic period
lift; the compatibility conditions are exactly its checked disc outputs. -/
theorem rootEval_analyticAt (hM : 1 < M)
    (he : intoAffine M M hM = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (t : ℂ → UpperHalfPlane) (ht : ∀ z, Admissible (t z))
    (F : ℂ → ℂ) (c : ℂ) (hF : AnalyticAt ℂ F c)
    (hFt : F =ᶠ[𝓝 c] (fun z => (t z : ℂ)))
    (hj : ∀ᶠ z in 𝓝 c, ActualQJ318.jInvariant (t z) = 1+z)
    (a : AdjoinRoot p) :
    AnalyticAt ℂ (fun z => rootEval M I e hb (t z) (ht z) s p ep a) c := by
  obtain ⟨f,rfl⟩ := AdjoinRoot.mk_surjective a
  have hX : AnalyticAt ℂ (fun z => SelectedMarkedPeriodCoordinate318.arithmeticX M (t z)) c := by
    have h0 : F c = (t c : ℂ) := hFt.self_of_nhds
    have ha := SelectedMarkedPeriodCoordinate318.arithmeticX_analyticAt M hM (t c) (ht c)
    rw [← h0] at ha
    apply (ha.comp hF).congr
    filter_upwards [hFt] with z hz
    change SelectedMarkedPeriodCoordinate318.arithmeticX M (UpperHalfPlane.ofComplex (F z)) = _
    rw [hz,UpperHalfPlane.ofComplex_apply]
  apply (eval_analyticAt (fun z => evaluation M (t z) (ht z)) _ c
    (coefficient_analyticAt M t ht c hj) hX f).congr
  exact Filter.Eventually.of_forall (fun z =>
    (rootEval_mk M I e hb (t z) (ht z) s hs p ep hep hM he f).symm)

section Complex

/-- A fixed complex domain for the whole germ. Individual period
evaluations have different R-algebra structures on ℂ, so use scalar
extension from ℤ rather than install one false common R-algebra instance. -/
@[expose] def extendComplex {B : Type*} [CommRing B] (f : B →+* ℂ) :
    ℂ ⊗[ℤ] B →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
    { toRingHom := f
      commutes' := fun n => by
        change f (n : B) = (n : ℂ)
        exact map_intCast f n }
    (fun a b => Commute.all a _)

theorem extendComplex_tmul {B : Type*} [CommRing B] (f : B →+* ℂ) (z : ℂ) (b : B) :
    extendComplex f (z ⊗ₜ[ℤ] b) = z * f b := rfl

theorem extendComplex_analyticAt {B : Type*} [CommRing B] (f : ℂ → B →+* ℂ)
    (c : ℂ) (hf : ∀ b, AnalyticAt ℂ (fun z => f z b) c) (a : ℂ ⊗[ℤ] B) :
    AnalyticAt ℂ (fun z => extendComplex (f z) a) c := by
  induction a using TensorProduct.induction_on with
  | zero =>
    have h0 : AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) c := analyticAt_const
    simpa only [map_zero] using h0
  | tmul a b =>
    have ha : AnalyticAt ℂ (fun _ : ℂ => a) c := analyticAt_const
    simpa only [extendComplex_tmul] using ha.mul (hf b)
  | add a b ha hb => simpa only [map_add] using ha.add hb

theorem complex_eval_j (t : UpperHalfPlane) (ht : Admissible t) :
    extendComplex (rootEval M I e hb t ht s p ep)
        ((1 : ℂ) ⊗ₜ[ℤ] (algebraMap (R M) (AdjoinRoot p) (OpenJModel318.jCoord M))) =
      ActualQJ318.jInvariant t := by
  rw [extendComplex_tmul,one_mul,rootEval_base,evaluation_jCoord]

end Complex
end SelectedPrimitiveCenteredGerm318

#print axioms SelectedPrimitiveCenteredGerm318.rootEval_analyticAt
#print axioms SelectedPrimitiveCenteredGerm318.extendComplex_analyticAt
#print axioms SelectedPrimitiveCenteredGerm318.complex_eval_j
