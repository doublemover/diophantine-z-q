module
public import OriginalBranchCotangentFiber318
public section
noncomputable section
namespace OriginalFiniteCotangentComparison318
open NumberField Polynomial OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open IntegralBranchCoordinates318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)
  (j : Fin 4) (φ : B (V c t v) (localTwists c t v hv) j →+* V c t v)
  (hφ : ∀ a : IntegralSourceBranches318.SourceOrder (V c t v) (localTwists c t v hv),
    algebraMap (V c t v) (K c t) (φ (algebraMap _ _ a))=
      IntegralValuativeGenericPoint318.sourceMap (V c t v) (K c t) (localTwists c t v hv)
        (t:K c t) (roots c t) (local_root_equations c t v hv) a)
@[expose] def evaluate := (algebraMap (V c t v) (K c t)).comp φ
@[expose] def two_unit : IsUnit (2:V c t v) :=
  IntegralSmoothProperBicanonical318.two_unit _ (ContactFinitePlaceBaseMap318.separation_unit c v hv)

include hφ in
theorem quartic_value : evaluate c t v hv j φ
    (IntegralBranchBicanonical318.sourceP (V c t v) (localTwists c t v hv) j)=
      OriginalBranchCotangentFiber318.quarticValue c t := by
  change algebraMap (V c t v) (K c t)
    (φ (algebraMap (IntegralSourceBranches318.SourceOrder (V c t v) (localTwists c t v hv)) _
      (algebraMap (Polynomial (V c t v)) _ (IntegralBranchBicanonical318.quartic (V c t v)))))=_
  rw [hφ,IntegralValuativeGenericPoint318.sourceMap_polynomial]
  simp only [IntegralBranchBicanonical318.quartic,map_prod,map_sub,Polynomial.aeval_X,
    Polynomial.aeval_C,OriginalBranchCotangentFiber318.quarticValue,ContactKummerOrder318.denominator]
  push_cast
  apply Finset.prod_congr rfl
  intro k hk
  congr 1
  fin_cases k <;> norm_num [IntegralSourceBranches318.contacts,LinearContactSquareclass318.contacts]

include hn hφ in
theorem quartic_ne : evaluate c t v hv j φ
    (IntegralBranchBicanonical318.sourceP (V c t v) (localTwists c t v hv) j)≠0 := by
  rw [quartic_value c t v hv j φ hφ]
  exact OriginalBranchCotangentFiber318.quartic_ne c t hn

abbrev LocalFiber := IntegralBranchCotangentFiber318.Fiber (V c t v) (localTwists c t v hv)
  j (K c t) (evaluate c t v hv j φ)
@[expose] def localFrame : LocalFiber c t v hv j φ ≃ₗ[K c t] K c t :=
  IntegralBranchCotangentFiber318.frame _ _ _ (two_unit c t v hv) _ (evaluate c t v hv j φ)
@[expose] def localDt : LocalFiber c t v hv j φ :=
  IntegralBranchCotangentFiber318.dt _ _ _ _ (evaluate c t v hv j φ)

include hn hφ in
theorem localDt_ne : localFrame c t v hv j φ (localDt c t v hv j φ)≠0 :=
  IntegralBranchCotangentFiber318.dt_ne _ _ _ (two_unit c t v hv) _ _
    (quartic_ne c t hn v hv j φ hφ)

variable (i : Fin 4)
/-- The actual relative cotangent fibers are compared by the ORIGINAL Dt.
This is a linear equivalence of scalar-extended Kähler modules, not a map
invented from the section-value ratio. -/
@[expose] def comparison : LocalFiber c t v hv j φ ≃ₗ[K c t]
    OriginalBranchCotangentFiber318.Fiber c t hn i :=
  CotangentParameterComparison318.comparison (localFrame c t v hv j φ)
    (OriginalBranchCotangentFiber318.frame c t hn i) (localDt c t v hv j φ)
    (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv j φ hφ) (OriginalBranchCotangentFiber318.dt_ne c t hn i)

theorem preserves_dt : comparison c t hn v hv j φ hφ i (localDt c t v hv j φ)=
    OriginalBranchCotangentFiber318.dt c t hn i :=
  CotangentParameterComparison318.comparison_parameter _ _ _ _ _ _

@[expose] def derivativeRatio : K c t :=
  OriginalBranchCotangentFiber318.frame c t hn i (OriginalBranchCotangentFiber318.dt c t hn i)/
    localFrame c t v hv j φ (localDt c t v hv j φ)

include hφ in
theorem derivativeRatio_ne : derivativeRatio c t hn v hv j φ i≠0 :=
  div_ne_zero (OriginalBranchCotangentFiber318.dt_ne c t hn i) (localDt_ne c t hn v hv j φ hφ)

include hφ in
/-- The scalar of the prior original-section comparison is now proved to
be the SQUARE of the actual Dt-preserving cotangent-fiber transition. -/
theorem original_zero : ContactBicanonicalPointHeight318.a0 c t hn i=
    (derivativeRatio c t hn v hv j φ i)^2 * evaluate c t v hv j φ
      (IntegralGlobalBicanonicalPair318.branchCoefficient (V c t v) (localTwists c t v hv) j 0) := by
  have ha := IntegralBranchCotangentFiber318.cleared_section (V c t v) (localTwists c t v hv)
    j (two_unit c t v hv) (K c t) (evaluate c t v hv j φ)
  rw [quartic_value c t v hv j φ hφ] at ha
  exact CotangentParameterComparison318.coefficient_transition
    (localFrame c t v hv j φ) (OriginalBranchCotangentFiber318.frame c t hn i)
    (localDt c t v hv j φ) (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv j φ hφ)
    (OriginalBranchCotangentFiber318.quarticValue c t) (VerticalSection318.J:K c t) _ _
    (OriginalBranchCotangentFiber318.quartic_ne c t hn) ha
    (OriginalBranchCotangentFiber318.cleared_original c t hn i)

include hφ in
theorem original_one : ContactBicanonicalPointHeight318.a1 c t hn i=
    (derivativeRatio c t hn v hv j φ i)^2 * evaluate c t v hv j φ
      (IntegralGlobalBicanonicalPair318.branchCoefficient (V c t v) (localTwists c t v hv) j 1) := by
  have ht : evaluate c t v hv j φ (sourceT (V c t v) (localTwists c t v hv) j)=(t:K c t) :=
    (hφ (algebraMap (Polynomial (V c t v)) _ X)).trans
      ((IntegralValuativeGenericPoint318.sourceMap_polynomial _ _ _ _ _ _ X).trans (Polynomial.aeval_X _))
  rw [ContactBicanonicalPointHeight318.ratio,original_zero c t hn v hv j φ hφ i,
    IntegralOriginalSectionRatios318.branch_coefficients,map_mul,ht]
  ring

include hφ in
/-- On actual cotangent fibers, the induced tensor-square equivalence sends
the ORIGINAL integral q0 fiber to the original rational-frame q0 fiber.
Thus the quadratic coefficient comparison is realized by a genuine linear
map of the fibers, not merely asserted as a scalar identity. -/
theorem square_preserves_zero :
    TensorProduct.congr (comparison c t hn v hv j φ hφ i) (comparison c t hn v hv j φ hφ i)
      (evaluate c t v hv j φ
        (IntegralGlobalBicanonicalPair318.branchCoefficient (V c t v) (localTwists c t v hv) j 0) •
        (TensorProduct.tmul (K c t)
          (IntegralBranchCotangentFiber318.coordinate (V c t v) (localTwists c t v hv) j (K c t)
            (evaluate c t v hv j φ))
          (IntegralBranchCotangentFiber318.coordinate (V c t v) (localTwists c t v hv) j (K c t)
            (evaluate c t v hv j φ))))=
      ContactBicanonicalPointHeight318.a0 c t hn i •
        TensorProduct.tmul (K c t) (OriginalBranchCotangentFiber318.coordinate c t hn i)
          (OriginalBranchCotangentFiber318.coordinate c t hn i) := by
  rw [original_zero c t hn v hv j φ hφ i]
  exact CotangentParameterComparison318.square_weighted
    (localFrame c t v hv j φ) (OriginalBranchCotangentFiber318.frame c t hn i)
    (localDt c t v hv j φ) (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv j φ hφ) (OriginalBranchCotangentFiber318.dt_ne c t hn i)
    _ _ (IntegralBranchCotangentFiber318.coordinate_value _ _ _ (two_unit c t v hv) _ _)
    (OriginalBranchCotangentFiber318.coordinate_value c t hn i) _

include hφ in
/-- The actual cotangent-fiber comparison now supplies the finite-place
bound directly, without a free common-frame scalar premise. -/
theorem original_bounds :
    (∀ n : Fin 2, v (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*
        (v ((derivativeRatio c t hn v hv j φ i)^2))⁻¹≤1) ∧
    max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i))=
        v ((derivativeRatio c t hn v hv j φ i)^2) :=
  FinitePlaceChartPairBounds318.branch_bound c v hv j φ _ _ _
    (pow_ne_zero 2 (derivativeRatio_ne c t hn v hv j φ hφ i))
    (original_zero c t hn v hv j φ hφ i) (original_one c t hn v hv j φ hφ i)
end OriginalFiniteCotangentComparison318
