module
public import ThreeJRamificationParameters318
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public section
noncomputable section
namespace ThreeJAnalyticRamificationDivisor318
open ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318
open ThreeJRamificationParameters318 ThreeJFullLocalDegree318
open ThreeProjectiveJPoints318 ThreeJAnalyticGerms318 ThreeJChartHolomorphy318
open ThreeCompactParameter318
set_option maxHeartbeats 1500000

abbrev Point := Points (R:=ℚ) (K:=ℂ)
local instance : DecidableEq Point := Classical.decEq _
local instance : TopologicalSpace Point := ProjectiveLineComplexTopology318.complexPointTopology
@[expose] def finitePoint (t : ℂ) : Point := chartPoint (R:=ℚ) 1 t
@[expose] def infinityPoint : Point := chartPoint (R:=ℚ) 0 (0:ℂ)

/-- The effective analytic ramification divisor on the actual projective
complex points. Its coefficient is proved below to be local degree minus one
in the original scheme charts, at every point including both cusps. -/
@[expose] def ramification : Point →₀ ℕ :=
  Finsupp.single (finitePoint 0) 2+Finsupp.single (finitePoint (-243)) 2+
  Finsupp.single (finitePoint rootPlus) 1+Finsupp.single (finitePoint rootMinus) 1

lemma finitePoint_injective : Function.Injective finitePoint := chartPoint_injective 1
lemma finitePoint_ne_infinity (t : ℂ) : finitePoint t ≠ infinityPoint := finite_ne_infinity t

lemma ramification_finite (t : ℂ) : ramification (finitePoint t)=ThreeJRamificationParameters318.multiplicity t := by
  classical
  simp [ramification,ThreeJRamificationParameters318.multiplicity,Finsupp.single_apply,finitePoint_injective.eq_iff,eq_comm]
lemma ramification_infinity : ramification infinityPoint=0 := by
  classical
  simp [ramification,Finsupp.single_apply,finitePoint_ne_infinity]

/-- Exhaustive divisor identification, with the local representative equal
to the literal scheme map on an entire coordinate neighborhood. -/
theorem every_point_local_degree (p : Point) :
    LocalDegreeCertificate p (ramification p+1) := by
  rcases finite_or_infinity p with ⟨t,ht⟩ | hp
  · subst p
    change LocalDegreeCertificate (finitePoint t) (ramification (finitePoint t)+1)
    rw [ramification_finite]
    by_cases hz : t=0
    · subst t
      rw [multiplicity_zero]
      exact finite_zero_certificate
    · rw [multiplicity_local_degree hz]
      exact finite_nonzero_certificate t hz
  · subst p
    change LocalDegreeCertificate infinityPoint (ramification infinityPoint+1)
    rw [ramification_infinity]
    exact infinity_certificate

theorem support_exact : ramification.support=
    {finitePoint 0,finitePoint (-243),finitePoint rootPlus,finitePoint rootMinus} := by
  classical
  ext p
  rw [Finsupp.mem_support_iff]
  rcases finite_or_infinity p with ⟨t,ht⟩ | hp
  · subst p
    change ramification (finitePoint t) ≠ 0 ↔
      finitePoint t ∈ {finitePoint 0,finitePoint (-243),finitePoint rootPlus,finitePoint rootMinus}
    rw [ramification_finite,multiplicity_nonzero_iff]
    simp only [Finset.mem_insert,Finset.mem_singleton,finitePoint_injective.eq_iff]
  · subst p
    change ramification infinityPoint ≠ 0 ↔
      infinityPoint ∈ {finitePoint 0,finitePoint (-243),finitePoint rootPlus,finitePoint rootMinus}
    have hn (t:ℂ) : infinityPoint ≠ finitePoint t := (finitePoint_ne_infinity t).symm
    simp [ramification_infinity,hn]

@[expose] def degree : (Point →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℕ)

/-- The complete ramification mass is six, not just an upper bound from
the quartic degree or a count of the two visible cusp points. -/
theorem degree_six : degree ramification=6 := by
  unfold ramification
  simp only [map_add,degree,Finsupp.liftAddHom_apply_single,AddMonoidHom.id_apply]

lemma finite_map {t : ℂ} (ht : t ≠ 0) : mapPoints (finitePoint t)=finitePoint (J t) := by
  have hd : Polynomial.aeval t ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
    rw [(finite_evaluations t).2]
    exact pow_ne_zero 3 ht
  rw [finitePoint,finite_formula t hd,←ActualThreeJChartConsumer318.finite_J]
  rfl

lemma zero_image : mapPoints (finitePoint 0)=infinityPoint := by
  change mapPoints (chartPoint (R:=ℚ) 1 (0:ℂ))=chartPoint (R:=ℚ) 0 (0:ℂ)
  rw [finite_numerator_formula 0 finiteN_zero_ne,finite_cusp_germ.2.1]
lemma neg243_image : mapPoints (finitePoint (-243))=finitePoint 0 := by
  rw [finite_map (by norm_num : (-243:ℂ) ≠ 0)]
  norm_num [J]
lemma rootPlus_image : mapPoints (finitePoint rootPlus)=finitePoint 1728 := by
  rw [finite_map rootPlus_ne_zero,
    (ThreeJEllipticOrders318.elliptic_fiber rootPlus_ne_zero).mpr D_rootPlus]
lemma rootMinus_image : mapPoints (finitePoint rootMinus)=finitePoint 1728 := by
  rw [finite_map rootMinus_ne_zero,
    (ThreeJEllipticOrders318.elliptic_fiber rootMinus_ne_zero).mpr D_rootMinus]

/-- Pushforward of the complete effective analytic ramification divisor
under the actual scheme-induced complex map, retaining multiplicities. -/
theorem branch_cycle : Finsupp.mapDomain mapPoints ramification=
    Finsupp.single infinityPoint 2+Finsupp.single (finitePoint 0) 2+
      Finsupp.single (finitePoint 1728) 2 := by
  simp only [ramification,Finsupp.mapDomain_add,Finsupp.mapDomain_single,
    zero_image,neg243_image,rootPlus_image,rootMinus_image]
  rw [add_assoc,←Finsupp.single_add]

/-- The degree-six divisor is compatible with the independently computed
degree of the exact generic-stalk pullback, with its nonidentity scalar action. -/
theorem degree_identity :
    letI := ThreeJActualGenericDegree318.pullbackAlgebra
    letI : Module ThreeJActualGenericDegree318.Projective.functionField
      ThreeJActualGenericDegree318.Projective.functionField :=
        ThreeJActualGenericDegree318.pullbackAlgebra.toModule
    degree ramification+2=2*Module.finrank
      ThreeJActualGenericDegree318.Projective.functionField
      ThreeJActualGenericDegree318.Projective.functionField := by
  letI := ThreeJActualGenericDegree318.pullbackAlgebra
  letI : Module ThreeJActualGenericDegree318.Projective.functionField
    ThreeJActualGenericDegree318.Projective.functionField :=
      ThreeJActualGenericDegree318.pullbackAlgebra.toModule
  rw [degree_six,ThreeJActualGenericDegree318.actual_generic_degree_four]

/-- Every nonzero coefficient maps to one of the three original branch
values, with the two quadratic roots both mapping to1728. -/
theorem branch_values (p : Point) (hp : p ∈ ramification.support) :
    mapPoints p=infinityPoint ∨ mapPoints p=finitePoint 0 ∨
      mapPoints p=finitePoint 1728 := by
  classical
  rw [support_exact] at hp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with h | h | h | h
  · subst p
    exact Or.inl zero_image
  · subst p
    exact Or.inr (Or.inl neg243_image)
  · subst p
    exact Or.inr (Or.inr rootPlus_image)
  · subst p
    exact Or.inr (Or.inr rootMinus_image)

/-- The divisor is transported back along the already proved original
compact modular biholomorphism, not a newly chosen bijection of point sets. -/
@[expose] def compactRamification : ActualThreeCuspFilling318.Filled →₀ ℕ :=
  Finsupp.comapDomain ActualThreeProjectivePoints318.compactPointHomeomorph ramification
    ActualThreeProjectivePoints318.compactPointHomeomorph.injective.injOn

theorem compact_coefficient (z : ActualThreeCuspFilling318.Filled) :
    compactRamification z=
      ramification (ActualThreeProjectivePoints318.compactPointHomeomorph z) := rfl

theorem compact_local_degree (z : ActualThreeCuspFilling318.Filled) :
    LocalDegreeCertificate (ActualThreeProjectivePoints318.compactPointHomeomorph z)
      (compactRamification z+1) := by
  rw [compact_coefficient]
  exact every_point_local_degree _

theorem actual_cusp_coefficients :
    compactRamification (ActualThreeCuspFilling318.cusp ActualThreeCuspExhaustion318.zeroEnd)=2 ∧
    compactRamification (ActualThreeCuspFilling318.cusp ActualThreeCuspExhaustion318.infinityEnd)=0 := by
  constructor
  · rw [compact_coefficient,ActualThreeProjectivePoints318.compactPointHomeomorph_zero]
    exact (ramification_finite 0).trans multiplicity_zero
  · rw [compact_coefficient,ActualThreeProjectivePoints318.compactPointHomeomorph_infinity]
    exact ramification_infinity

end ThreeJAnalyticRamificationDivisor318
