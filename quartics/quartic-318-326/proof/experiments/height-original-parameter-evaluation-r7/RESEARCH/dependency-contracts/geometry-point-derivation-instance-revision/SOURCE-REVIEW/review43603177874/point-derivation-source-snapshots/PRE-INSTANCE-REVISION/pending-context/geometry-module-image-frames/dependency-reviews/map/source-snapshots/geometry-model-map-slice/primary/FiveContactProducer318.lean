module
public import ContactHeight318
public import CMContactAssembly318
public import SourceNonCMHeight318
public section
noncomputable section
namespace FiveContactProducer318
open ContactRadical318 ContactHeight318 NumberField SourceJacobianBound318
set_option maxHeartbeats 0

/-- The literal support parameter, not an arbitrary real dominating the radical. -/
@[expose] def support (u v:ℤ) : ℝ := (badProduct:ℝ)*(radical u v:ℝ)

theorem support_ge_one (u v:ℤ) : 1≤support u v := by
  have hb : (1:ℝ)≤badProduct := by rw [bad_product_exact]; norm_num
  have hr : (1:ℝ)≤radical u v := by exact_mod_cast radical_pos u v
  unfold support
  nlinarith

/-- The metric coordinate s=u/v has exactly the source's actual projective height. -/
theorem pointHeight_eq_contact_height (u v:ℤ) :
    pointHeight u v=absLogHeight₁ ((u:ℚ)/(v:ℚ)) := by
  rw [DetectorHeightTransfer318.rational_height_eq,Height.logHeight₁_div_eq_logHeight]
  rfl

/-- The metric uses t=32s; dividing by32 returns the literal contact coordinate. -/
theorem scaled_metric_height (u v:ℤ) :
    absLogHeight₁ ((32*((u:ℚ)/(v:ℚ)))/32)=pointHeight u v := by
  rw [show (32*((u:ℚ)/(v:ℚ)))/32=(u:ℚ)/(v:ℚ) by ring]
  exact (pointHeight_eq_contact_height u v).symm

/-- The literal five nonzero homogeneous forms put the source point outside
all five actual branch contacts, including the infinity chart. -/
theorem source_contact_avoidance (u v:ℤ) (hn:∀j:Fin 5,forms u v j≠0) :
    v≠0 ∧ (u:ℚ)/(v:ℚ)≠0 ∧ (u:ℚ)/(v:ℚ)≠1 ∧
      (u:ℚ)/(v:ℚ)≠2401 ∧ (u:ℚ)/(v:ℚ)≠ -343/32 := by
  have hv:v≠0 := by simpa [forms] using hn 0
  have hu:u≠0 := by simpa [forms] using hn 1
  have h1:u-v≠0 := by simpa [forms] using hn 2
  have h2:u-2401*v≠0 := by simpa [forms] using hn 3
  have h3:32*u+343*v≠0 := by simpa [forms] using hn 4
  have hvQ:(v:ℚ)≠0 := by exact_mod_cast hv
  refine ⟨hv,div_ne_zero (by exact_mod_cast hu) hvQ,?_,?_,?_⟩
  · intro h
    have he := (div_eq_iff hvQ).mp h
    apply h1
    have : (u:ℚ)-(v:ℚ)=0 := by linarith
    exact_mod_cast this
  · intro h
    have he := (div_eq_iff hvQ).mp h
    apply h2
    have : (u:ℚ)-2401*(v:ℚ)=0 := by linarith
    exact_mod_cast this
  · intro h
    have he := (div_eq_iff hvQ).mp h
    apply h3
    have : 32*(u:ℚ)+343*(v:ℚ)=0 := by linarith
    exact_mod_cast this

/-- CM geometric realization data. Every field is a producer input: the final
surface854R and contact-height bounds are absent. -/
structure CMData (u v:ℤ) where
  discriminant:ℤ
  baseDiscriminant:ℕ
  averagingDegree:ℕ
  period:Fin averagingDegree→ℂ
  fieldDegree:ℝ
  isogenyDegree:ℝ
  ellipticHeight:ℝ
  productHeight:ℝ
  surfaceHeight:ℝ
  fundamental:Int.IsFundamentalDiscr discriminant
  baseDiscriminant_ne:baseDiscriminant≠0
  prime_support:∀p:ℕ,p.Prime→p∣discriminant.natAbs→p∣baseDiscriminant
  radical_support:(CMDiscriminant318.radical baseDiscriminant:ℝ)≤support u v
  averaging_pos:1≤averagingDegree
  reduced_lower:∀i,Real.sqrt 3/2≤(period i).im
  reduced_upper:∀i,(period i).im≤Real.sqrt discriminant.natAbs/2
  silverman:ellipticHeight=(∑i,CMArchimedean318.summand (period i))/(averagingDegree:ℝ)
  product:productHeight=2*ellipticHeight
  field_pos:0<fieldDegree
  field_bound:fieldDegree≤576
  isogeny_pos:0 < isogenyDegree
  isogeny_bound:isogenyDegree≤(CMIsogeny318.Xi fieldDegree productHeight)^2
  variation:surfaceHeight≤productHeight+(1/2)*Real.log isogenyDegree
  contact_metric:pointHeight u v≤2*surfaceHeight+120

theorem CMData.bound {u v:ℤ} (D:CMData u v) :
    pointHeight u v<2^68*((210:ℝ)^300)^2*(support u v)^((49:ℝ)/8)+128 := by
  exact CMContactAssembly318.original_contact_bound D.discriminant D.baseDiscriminant
    D.averagingDegree D.period (support u v) D.fieldDegree D.isogenyDegree
    D.ellipticHeight D.productHeight D.surfaceHeight (pointHeight u v) D.fundamental
    D.baseDiscriminant_ne D.prime_support D.radical_support (support_ge_one u v)
    D.averaging_pos D.reduced_lower D.reduced_upper D.silverman D.product D.field_pos
    D.field_bound D.isogeny_pos D.isogeny_bound D.variation D.contact_metric

/-- Non-CM geometric realization data. Actual cusp functions, disc energies,
finite intersection data and Arakelov identities replace a final Jacobian-height premise.
K is the auxiliary semistable/fiber averaging field, not the bounded isogeny field. -/
structure NonCMData (K:Type*) [Field K] [NumberField K] (u v:ℤ) where
  genus:ℕ
  candidate:ℕ
  coverDegree:ℕ
  level:ℕ
  exceptionalCount:ℕ
  outsideCount:ℕ
  cusp:CuspArakelovData318.Data K genus candidate level
  finiteData:FiniteData (Fin exceptionalCount) (Fin outsideCount)
    (2^128+candidate) coverDegree level
  arakelov:SourceNonCMHeight318.ArakelovIdentifications K cusp finiteData
  genus_lower:2≤genus
  candidate_bound:candidate≤genus^3+1
  genus_degree:genus≤coverDegree
  level_pos:1≤level
  index_bound:(coverDegree:ℝ)<2^14*ActualLogWeight318.C*(support u v)^((97:ℝ)/32)
  level_bound:(level:ℝ)≤ActualLogWeight318.C*(support u v)^2
  isogenyFieldDegree:ℝ
  imageHeight:ℝ
  surfaceHeight:ℝ
  image_bound:imageHeight≤arakelov.hGR+3*(genus:ℝ)/2
  field_pos:0 < isogenyFieldDegree
  field_bound:isogenyFieldDegree≤2304*support u v
  isogeny_variation:surfaceHeight≤ imageHeight+
    8*(32*Real.log 14+Real.log isogenyFieldDegree+
      Real.log (max 1 (max (Real.log isogenyFieldDegree) imageHeight)))
  contact_metric:pointHeight u v≤2*surfaceHeight+120

theorem NonCMData.bound {K:Type*} [Field K] [NumberField K] {u v:ℤ}
    (D:NonCMData K u v) :
    pointHeight u v<2^68*((210:ℝ)^300)^2*(support u v)^((49:ℝ)/8)+128 := by
  exact SourceNonCMHeight318.nonCM_contact_49_over_8 K D.cusp D.finiteData D.arakelov
    D.genus_lower D.candidate_bound D.genus_degree D.level_pos (support u v)
    (support_ge_one u v) D.index_bound D.level_bound D.isogenyFieldDegree
    D.imageHeight D.surfaceHeight (pointHeight u v) D.image_bound D.field_pos
    D.field_bound D.isogeny_variation D.contact_metric

/-- Precisely the remaining global realization obligation. It requires actual
producer data for every primitive contact point; it is not asserted here. -/
@[expose] def GeometricRealization : Prop := ∀u v:ℤ, IsCoprime u v →
    (∀j:Fin 5,forms u v j≠0) →
    Nonempty (CMData u v) ∨
      ∃(K:Type) (f:Field K) (nf:@NumberField K f),
        Nonempty (@NonCMData K f nf u v)

/-- Complete finite/analytic assembly into the exact final source predicate.
The unconstructed algebraic geometry remains the explicit realization input. -/
theorem five_contact_of_realization (h:GeometricRealization) : FiveContact49Height := by
  intro u v hc hn
  rcases h u v hc hn with hm | hncm
  · obtain ⟨D⟩ := hm
    exact D.bound
  · obtain ⟨K, f, nf, hD⟩ := hncm
    letI := f
    letI := nf
    obtain ⟨D⟩ := hD
    exact D.bound

end FiveContactProducer318
