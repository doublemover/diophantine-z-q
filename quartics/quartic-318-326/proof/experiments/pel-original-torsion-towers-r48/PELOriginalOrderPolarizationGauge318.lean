module
public import PELOriginalOrderPolarizationFrames318
public section
noncomputable section
namespace PELOriginalOrderPolarizationGauge318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalOrderPolarizationData318 PELOriginalOrderPolarizationFrames318
variable (τ : ℂ) (hτ : 0 < τ.im) (D : Data τ hτ) (a : PELPrincipalOrderCoordinates318.order)

/-- Whole regular cocycle comparison from genuinely regular even order-product
sections. All prime points of the order/complement triple cover are retained. -/
lemma gauge_equation (b c : Index τ hτ) :
    (LineFrameCocycle318.cocycle (originalPower τ hτ D a) (chart τ hτ a)
      (sourceFrame τ hτ D a)).transition b c=
    UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (candidate τ hτ)).obj
      (chart τ hτ a) (unit τ hτ D a) b c *
      (LineFrameCocycle318.cocycle (productSheaf τ hτ D a) (chart τ hτ a)
        (productFrame τ hτ D a)).transition b c := by
  let W := chart τ hτ a b ⊓ chart τ hτ a c
  apply PELOriginalOpenFunctionSeparation318.unit_ext τ hτ W
  intro z hz
  have hb := (domain_iff τ hτ a b z).mp hz.1
  have hc := (domain_iff τ hτ a c z).mp hz.2
  rw [source_transition τ hτ D a b c z hz]
  have hu (u : Γ(candidate τ hτ,W)ˣ) :
      evaluation τ hτ W z hz (u⁻¹).val=(evaluation τ hτ W z hz u.val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using
      congrArg Units.val (map_inv (Units.map (evaluation τ hτ W z hz).toMonoidHom) u)
  simp only [UnitTransitionCocycle318.coboundary,Units.val_mul,Units.coe_map]
  rw [value_eq_evaluation τ hτ W _ z hz,map_mul,map_mul,hu]
  rw [←value_eq_evaluation τ hτ W _ z hz,←value_eq_evaluation τ hτ W _ z hz,
    ←value_eq_evaluation τ hτ W _ z hz]
  rw [value_restrict,value_restrict,unit_value,unit_value,
    regular_value τ hτ D a b z hz.1,regular_value τ hτ D a c z hz.2,
    product_transition τ hτ D a b c z hz]
  have h0 := D.lineData.nonzero b.1 z hb.1
  have h1 := D.lineData.nonzero b.2.1 (PELOriginalComplementaryHermitian318.linear a z) hb.2.1
  have h2 := D.lineData.nonzero b.2.2 (PELOriginalComplementaryHermitian318.linear (PELOriginalComplementaryOrder318.complement a) z) hb.2.2
  have h3 := D.lineData.nonzero c.1 z hc.1
  have h4 := D.lineData.nonzero c.2.1 (PELOriginalComplementaryHermitian318.linear a z) hc.2.1
  have h5 := D.lineData.nonzero c.2.2 (PELOriginalComplementaryHermitian318.linear (PELOriginalComplementaryOrder318.complement a) z) hc.2.2
  simp only [div_pow]
  field_simp [h0,h1,h2,h3,h4,h5]

/-- Actual even order/complement power isomorphism, constructed from independently
regular coefficients and whole module-sheaf cocycle reconstruction. -/
@[expose] def iso : productSheaf τ hτ D a ≅ originalPower τ hτ D a :=
  FramedLineUnitGaugeIso318.iso _ _ (chart τ hτ a) (productFrame τ hτ D a)
    (sourceFrame τ hτ D a) (covers τ hτ a) (unit τ hτ D a)
    (gauge_equation τ hτ D a)
lemma hom_inv : (iso τ hτ D a).hom≫(iso τ hτ D a).inv=𝟙 _ := (iso τ hτ D a).hom_inv_id
lemma inv_hom : (iso τ hτ D a).inv≫(iso τ hτ D a).hom=𝟙 _ := (iso τ hτ D a).inv_hom_id
end PELOriginalOrderPolarizationGauge318
