module
public import IntegralRationalOpenComparison318
public import ContactGlobalBicanonical318
public section
noncomputable section
namespace GlobalBicanonicalOpenRestriction318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOverlapIntrinsic318 ContactFiniteOverlapDifferential318
open IntegralRationalOpenComparison318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def openSet : (ContactGlobalSmooth318.Model c).Opens := embedding c ''ᵁ ⊤
@[expose] def dtSection (a : O c) : Γ(ContactGlobalBicanonical318.tensor c, openSet c) :=
  IntrinsicTensorChartSections318.weightedSquare
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c) a
    (KaehlerDifferential.D ℚ (O c) (ContactUnbranchedDifferentialFrame318.coordinate c))

theorem originalProduct_eq : originalProduct c = P c :=
  (SourceOpenFractionField318.orderToOpen_on_polynomial c ContactKummerOrder318.denominator).symm

theorem P_inverse : P c * originalInverse c = 1 := by
  rw [←originalProduct_eq]
  unfold originalProduct originalInverse
  rw [←map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- Actual equality of intrinsic sections on the full original open. The
quartic is a unit on this whole open, so no dense-open extension is assumed. -/
theorem branch_dt (i : Fin 4) : finiteQ0 c i = dtSection c (originalInverse c) := by
  apply IntrinsicTensorChartSections318.weightedSquare_agreement
    (R := ℚ) (S := O c) (embedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (over_Q c) (P c)
    (ContactOverlapAlgebraMaps318.branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i))
    (factor c i) (originalInverse c) 1
    (KaehlerDifferential.D ℚ (O c) (z c i))
    (KaehlerDifferential.D ℚ (O c) (ContactUnbranchedDifferentialFrame318.coordinate c))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.t c))
  · exact P_unit c
  · exact coefficient_cleared c i
  · simpa only [one_pow] using P_inverse c
  · exact differential_relation c i
  · exact (one_smul _ _).symm

/-- Restriction of the exact previously glued global first section. -/
theorem q0_restrict :
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op (ContactGlobalBicanonical318.q0 c) =
      dtSection c (originalInverse c) := by
  have h := congrArg
    ((ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (ContactFiniteTensorRestrictions318.branchLE c 0)).op)
    (ContactGlobalBicanonical318.q0_restrict c (some 0))
  have h' := h.trans ((ContactFiniteTensorRestrictions318.q0_restrict c 0).trans (branch_dt c 0))
  simpa only [←(ContactGlobalBicanonical318.tensor c).presheaf.map_comp_apply,
    ←op_comp, homOfLE_comp] using h'

/-- Multiplication by the original coordinate in the same actual structure
sheaf agrees with coefficient multiplication, not an unrelated scalar action. -/
theorem dt_coordinate (a : O c) :
    dtSection c (ContactUnbranchedDifferentialFrame318.coordinate c * a) =
      ContactCommonTensorSections318.tFunction c • dtSection c a :=
  IntrinsicTensorChartSections318.weightedSquare_mul _ _ _ _ _ _

/-- Restriction of the exact previously glued second section, retaining t. -/
theorem q1_restrict :
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op (ContactGlobalBicanonical318.q1 c) =
      dtSection c (ContactUnbranchedDifferentialFrame318.coordinate c * originalInverse c) := by
  have h := congrArg
    ((ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (ContactFiniteTensorRestrictions318.branchLE c 0)).op)
    (ContactGlobalBicanonical318.q1_restrict c (some 0))
  have hr := (ContactFiniteTensorRestrictions318.q1_restrict c 0).trans
    ((ContactCommonTensorSections318.finiteQ1_relation c 0).trans
      ((congrArg (fun s => ContactCommonTensorSections318.tFunction c • s) (branch_dt c 0)).trans
        (dt_coordinate c (originalInverse c)).symm))
  have h' := h.trans hr
  simpa only [←(ContactGlobalBicanonical318.tensor c).presheaf.map_comp_apply,
    ←op_comp, homOfLE_comp] using h'

/-- Natural-number scaling is scaling of the actual intrinsic section. -/
theorem dt_nsmul (n : ℕ) (a : O c) : dtSection c ((n : O c) * a) = n • dtSection c a := by
  unfold dtSection IntrinsicTensorChartSections318.weightedSquare
  simp only [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]

/-- The actual J²-scaled global first section restricts to exactly the
coefficient produced by the integral chart under the verified equivalence. -/
theorem scaled_q0_restrict :
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op
      ((2765952000 : ℕ)^2 • ContactGlobalBicanonical318.q0 c) =
      dtSection c (comparison c (IntegralContactOpenSections318.coefficient0 ℚ c)) := by
  rw [map_nsmul, q0_restrict, comparison_coefficient0, ←dt_nsmul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem scaled_q1_restrict :
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op
      ((2765952000 : ℕ)^2 • ContactGlobalBicanonical318.q1 c) =
      dtSection c (comparison c (IntegralContactOpenSections318.coefficient1 ℚ c)) := by
  rw [map_nsmul, q1_restrict, comparison_coefficient1, ←dt_nsmul]
  congr 1
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The actual integral chart's weighted differential expression, carried
through the verified rational algebra map and its genuine differential map,
then realized in the original ambient intrinsic tensor sheaf. -/
@[expose] def integralExpression (a : IntegralContactOpenFrame318.Order ℚ c) :
    Γ(ContactGlobalBicanonical318.tensor c, openSet c) :=
  IntrinsicTensorChartSections318.weightedSquare
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (comparison c a)
    (AlgHomDifferential318.map (comparisonAlg c).toAlgHom
      (KaehlerDifferential.D ℚ (IntegralContactOpenFrame318.Order ℚ c)
        (IntegralContactOpenFrame318.coordinate ℚ c)))

theorem integralExpression_eq (a : IntegralContactOpenFrame318.Order ℚ c) :
    integralExpression c a = dtSection c (comparison c a) := by
  unfold integralExpression
  rw [comparison_differential]
  rfl

/-- The original global sections, not just their independently assigned
coefficients, agree with both actual integral-chart expressions on this open. -/
theorem scaled_global_pair :
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op
      ((2765952000 : ℕ)^2 • ContactGlobalBicanonical318.q0 c) =
        integralExpression c (IntegralContactOpenSections318.coefficient0 ℚ c) ∧
    (ContactGlobalBicanonical318.tensor c).presheaf.map
      (homOfLE (show openSet c ≤ ⊤ from le_top)).op
      ((2765952000 : ℕ)^2 • ContactGlobalBicanonical318.q1 c) =
        integralExpression c (IntegralContactOpenSections318.coefficient1 ℚ c) := by
  simpa only [integralExpression_eq] using
    And.intro (scaled_q0_restrict c) (scaled_q1_restrict c)

end GlobalBicanonicalOpenRestriction318
