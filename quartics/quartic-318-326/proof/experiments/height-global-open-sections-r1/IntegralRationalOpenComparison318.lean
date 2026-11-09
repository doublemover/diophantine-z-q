module
public import IntegralContactOpenSections318
public import ContactUnbranchedDifferentialFrame318
public section
noncomputable section
namespace IntegralRationalOpenComparison318
open Polynomial
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

theorem contact_eq (i : Fin 4) :
    (IntegralContactOpenFrame318.contacts i : ℚ) = LinearContactSquareclass318.contacts i := by
  fin_cases i <;> norm_num [IntegralContactOpenFrame318.contacts, LinearContactSquareclass318.contacts]

theorem denominator_eq : IntegralContactOpenFrame318.denominator ℚ =
    ContactKummerOrder318.denominator := by
  unfold IntegralContactOpenFrame318.denominator ContactKummerOrder318.denominator
  simp_rw [contact_eq]

theorem coefficient_eq (i : Fin 4) : IntegralContactOpenFrame318.coefficient ℚ c i =
    ContactKummerOrder318.coefficient c i := by
  unfold IntegralContactOpenFrame318.coefficient ContactKummerOrder318.coefficient
  rw [contact_eq]

/-- Exact denominator and inverse in the existing original rational order. -/
@[expose] def originalProduct : ContactKummerOrder318.OpenOrder c :=
  algebraMap ContactKummerOrder318.OpenBase (ContactKummerOrder318.OpenOrder c)
    (algebraMap ℚ[X] ContactKummerOrder318.OpenBase ContactKummerOrder318.denominator)
@[expose] def originalInverse : ContactKummerOrder318.OpenOrder c :=
  algebraMap ContactKummerOrder318.OpenBase (ContactKummerOrder318.OpenOrder c)
    (IsLocalization.Away.invSelf ContactKummerOrder318.denominator)

/-- The actual rings, coordinate, inverted product and inverse are identified
at once. This is not a cardinality comparison or a fresh isomorphic cover
whose coordinate has been left unspecified. -/
theorem exists_comparison : ∃ e : IntegralContactOpenFrame318.Order ℚ c ≃+*
    ContactKummerOrder318.OpenOrder c,
    e (IntegralContactOpenFrame318.coordinate ℚ c) =
      ContactUnbranchedDifferentialFrame318.coordinate c ∧
    e (IntegralContactOpenSections318.poleProduct ℚ c) = originalProduct c ∧
    e (IntegralContactOpenSections318.inverseProduct ℚ c) = originalInverse c := by
  unfold IntegralContactOpenFrame318.coordinate IntegralContactOpenSections318.poleProduct
    IntegralContactOpenSections318.inverseProduct IntegralContactOpenFrame318.Order
    IntegralContactOpenFrame318.Base
  simp_rw [denominator_eq, coefficient_eq]
  exact ⟨RingEquiv.refl _, rfl, rfl, rfl⟩

@[expose] def comparison : IntegralContactOpenFrame318.Order ℚ c ≃+*
    ContactKummerOrder318.OpenOrder c := (exists_comparison c).choose

theorem comparison_coordinate : comparison c (IntegralContactOpenFrame318.coordinate ℚ c) =
    ContactUnbranchedDifferentialFrame318.coordinate c := (exists_comparison c).choose_spec.1

theorem comparison_product : comparison c (IntegralContactOpenSections318.poleProduct ℚ c) =
    originalProduct c := (exists_comparison c).choose_spec.2.1

theorem comparison_inverse : comparison c (IntegralContactOpenSections318.inverseProduct ℚ c) =
    originalInverse c := (exists_comparison c).choose_spec.2.2

/-- Exact original rational coefficient of the J²-scaled first section. -/
theorem comparison_coefficient0 :
    comparison c (IntegralContactOpenSections318.coefficient0 ℚ c) =
      (2765952000 : ContactKummerOrder318.OpenOrder c)^2 * originalInverse c := by
  simp only [IntegralContactOpenSections318.coefficient0, map_mul, map_pow, map_ofNat,
    comparison_inverse]

theorem comparison_coefficient1 :
    comparison c (IntegralContactOpenSections318.coefficient1 ℚ c) =
      ContactUnbranchedDifferentialFrame318.coordinate c *
        ((2765952000 : ContactKummerOrder318.OpenOrder c)^2 * originalInverse c) := by
  rw [IntegralContactOpenSections318.coefficient1, map_mul,
    comparison_coordinate, comparison_coefficient0]

/-- The ring comparison respects the original rational scalar structure. -/
@[expose] def comparisonAlg : IntegralContactOpenFrame318.Order ℚ c ≃ₐ[ℚ]
    ContactKummerOrder318.OpenOrder c :=
  { comparison c with commutes' := fun q => RingHom.map_rat_algebraMap _ q }

/-- The actual relative universal differential is transported to the
original dt, with the original coordinate retained. -/
theorem comparison_differential :
    AlgHomDifferential318.map (comparisonAlg c).toAlgHom
      (KaehlerDifferential.D ℚ (IntegralContactOpenFrame318.Order ℚ c)
        (IntegralContactOpenFrame318.coordinate ℚ c)) =
      KaehlerDifferential.D ℚ (ContactKummerOrder318.OpenOrder c)
        (ContactUnbranchedDifferentialFrame318.coordinate c) := by
  rw [AlgHomDifferential318.map_D]
  exact congrArg (KaehlerDifferential.D ℚ (ContactKummerOrder318.OpenOrder c))
    (comparison_coordinate c)

end IntegralRationalOpenComparison318
