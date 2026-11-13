module
public import PELOriginalEntireTranslationCharacter318
public section
noncomputable section
namespace HolomorphicTranslationGauge318
open QuaternionicRealPeriod318 Set Filter Topology
universe u
variable {ι : Type u} (L : AddSubgroup ComplexVectors) (δ : ComplexVectors)

/-- Local regular-unit data after specialization, with its FULL two-sided
frame equation. The actual sheaf-isomorphism producer must supply this
record; no global entire function or lattice character is a field. -/
structure Data where
  domain : ι → Set ComplexVectors
  isOpen_domain : ∀ i,IsOpen (domain i)
  cover : ∀ z,∃ i,z∈domain i
  gauge : ι → ComplexVectors → ℂ
  gauge_ne : ∀ i z,z∈domain i → gauge i z≠0
  gauge_diff : ∀ i z,z∈domain i → DifferentiableAt ℂ (gauge i) z
  stable : ∀ i (l : L) z,z∈domain i → z+l.val∈domain i
  factor : L → ComplexVectors → ℂ
  factor_ne : ∀ l z,factor l z≠0
  gauge_shift : ∀ i (l : L) z,z∈domain i →
    gauge i (z+l.val)=factor l z*gauge i z
  coefficient : (ι × ι) → ComplexVectors → ℂ
  coefficient_ne : ∀ a z,z∈domain a.1 → z+δ∈domain a.2 → coefficient a z≠0
  coefficient_diff : ∀ a z,z∈domain a.1 → z+δ∈domain a.2 →
    DifferentiableAt ℂ (coefficient a) z
  coefficient_periodic : ∀ a (l : L) z,z∈domain a.1 → z+δ∈domain a.2 →
    coefficient a (z+l.val)=coefficient a z
  compatibility : ∀ a b z,z∈domain a.1 → z+δ∈domain a.2 →
    z∈domain b.1 → z+δ∈domain b.2 →
    coefficient a z*(gauge b.1 z/gauge a.1 z)=
      (gauge b.2 (z+δ)/gauge a.2 (z+δ))*coefficient b z

variable (D : Data L δ)
@[expose] def localDomain (a : ι × ι) : Set ComplexVectors :=
  D.domain a.1 ∩ (fun z => z+δ) ⁻¹' D.domain a.2
lemma localDomain_open (a : ι × ι) : IsOpen (localDomain L δ D a) :=
  (D.isOpen_domain a.1).inter ((D.isOpen_domain a.2).preimage (continuous_id.add continuous_const))
lemma local_cover (z : ComplexVectors) : ∃ a,z∈localDomain L δ D a := by
  obtain ⟨i,hi⟩ := D.cover z
  obtain ⟨j,hj⟩ := D.cover (z+δ)
  exact ⟨(i,j),hi,hj⟩
@[expose] def localValue (a : ι × ι) (z : ComplexVectors) : ℂ :=
  D.coefficient a z*D.gauge a.2 (z+δ)/D.gauge a.1 z

lemma local_agree (a b : ι × ι) (z : ComplexVectors)
    (ha : z∈localDomain L δ D a) (hb : z∈localDomain L δ D b) :
    localValue L δ D a z=localValue L δ D b z := by
  have h := D.compatibility a b z ha.1 ha.2 hb.1 hb.2
  have h1 := D.gauge_ne a.1 z ha.1
  have h2 := D.gauge_ne a.2 (z+δ) ha.2
  have h3 := D.gauge_ne b.1 z hb.1
  dsimp only [localValue]
  field_simp [h1,h2,h3] at h ⊢
  linear_combination h

@[expose] def entireValue (z : ComplexVectors) : ℂ :=
  localValue L δ D (local_cover L δ D z).choose z
lemma value_on (a : ι × ι) (z : ComplexVectors) (ha : z∈localDomain L δ D a) :
    entireValue L δ D z=localValue L δ D a z :=
  local_agree L δ D _ a z (local_cover L δ D z).choose_spec ha

lemma nonzero (z : ComplexVectors) : entireValue L δ D z≠0 := by
  obtain ⟨a,ha⟩ := local_cover L δ D z
  rw [value_on L δ D a z ha]
  exact div_ne_zero (mul_ne_zero (D.coefficient_ne a z ha.1 ha.2)
    (D.gauge_ne a.2 (z+δ) ha.2)) (D.gauge_ne a.1 z ha.1)

/-- Ordinary entire holomorphy is derived by open gluing of the actual
local coefficients and theta gauges, not assigned to a chosen quotient. -/
lemma differentiable : Differentiable ℂ (entireValue L δ D) := by
  intro z
  obtain ⟨a,ha⟩ := local_cover L δ D z
  have hd : DifferentiableAt ℂ (localValue L δ D a) z :=
    ((D.coefficient_diff a z ha.1 ha.2).mul
      ((D.gauge_diff a.2 (z+δ) ha.2).comp z (differentiableAt_id.add_const δ))).div
        (D.gauge_diff a.1 z ha.1) (D.gauge_ne a.1 z ha.1)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(localDomain_open L δ D a).mem_nhds ha] with w hw
  exact value_on L δ D a w hw

lemma shift (l : L) (z : ComplexVectors) :
    entireValue L δ D (z+l.val)=
      (D.factor l (z+δ)/D.factor l z)*entireValue L δ D z := by
  obtain ⟨a,ha⟩ := local_cover L δ D z
  have hb : z+l.val∈localDomain L δ D a :=
    ⟨D.stable a.1 l z ha.1,by
      simpa only [add_assoc,add_left_comm,add_comm] using D.stable a.2 l (z+δ) ha.2⟩
  rw [value_on L δ D a _ hb,value_on L δ D a _ ha]
  dsimp only [localValue]
  rw [D.coefficient_periodic a l z ha.1 ha.2,D.gauge_shift a.1 l z ha.1,
    show z+l.val+δ=(z+δ)+l.val by abel,D.gauge_shift a.2 l (z+δ) ha.2]
  field_simp [D.factor_ne l z,D.gauge_ne a.1 z ha.1]
end HolomorphicTranslationGauge318
