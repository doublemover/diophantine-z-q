module
public import SameSurfaceFiveContactBridge318
public section
noncomputable section
namespace ActualCMFiberContactEndpoint318
open NumberField ContactHeight318 FiveContactProducer318 RefinedContactRealization318
open ActualPELMetricSections318 SameSurfaceFiveContactBridge318

/-- The strict linear radical estimate on the actual chosen CM branch. D has
no final surface or contact bound field. Hodge data come from the selected A,
not the isogenous auxiliary product. Separate section and controlled fields
are not identified. -/
theorem original_linear {L : Type*} [Field L] [NumberField L] {u v : ℤ}
    (D : CMInputs u v) {y : ℝ} (T : Datum L u v y)
    (hcmp : y-Real.log Real.pi≤D.surfaceHeight) :
    pointHeight u v<1708*support u v+120 := by
  have hA := CMProducer318.original_surface_bound D.discriminant D.baseDiscriminant
    D.averagingDegree D.period (support u v) D.fieldDegree D.isogenyDegree
    D.ellipticHeight D.productHeight D.surfaceHeight D.fundamental D.baseDiscriminant_ne
    D.prime_support D.radical_support (support_ge_one u v) D.averaging_pos
    D.reduced_lower D.reduced_upper D.silverman D.product D.field_pos D.field_bound
    D.isogeny_pos D.isogeny_bound D.variation
  have hcontact := (metricSections T).original_bound
  linarith

theorem target {L : Type*} [Field L] [NumberField L] {u v : ℤ}
    (D : CMInputs u v) {y : ℝ} (T : Datum L u v y)
    (hcmp : y-Real.log Real.pi≤D.surfaceHeight) :
    pointHeight u v<2^68*((210:ℝ)^300)^2*(support u v)^((49:ℝ)/8)+128 := by
  have hcontact := (metricSections T).original_bound
  exact (cmFromBound D (by linarith)).bound

end ActualCMFiberContactEndpoint318
