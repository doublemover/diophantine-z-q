module
public import SelectedGammaOneQuotientArea318
public import SelectedWeightTwoPetersson318
public import SelectedStandardModularFiniteVolume318
public import Mathlib.NumberTheory.ModularForms.Bounds
public section
noncomputable section

open UpperHalfPlane MeasureTheory Set Matrix
open scoped ENNReal BigOperators Pointwise MatrixGroups Classical
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318
open SelectedGammaOneQuotientArea318 SelectedStandardModularFiniteVolume318
open SelectedWeightTwoPetersson318

namespace SelectedGammaOneFinitePetersson318

private abbrev Modular := SL(2,ℤ)
private abbrev SignedLevel (N : ℕ) := CongruenceSubgroup.Gamma1 N

private theorem coset_decompose (N : ℕ) (g : Modular) :
    ∃ h : SignedLevel N,
      (Quotient.out (QuotientGroup.mk g : Modular ⧸ SignedLevel N) : Modular) * h.val = g := by
  let q : Modular ⧸ SignedLevel N := QuotientGroup.mk g
  let r : Modular := Quotient.out q
  have hh : r⁻¹ * g ∈ SignedLevel N :=
    QuotientGroup.leftRel_apply.mp
      (@Quotient.exact' _ (QuotientGroup.leftRel (SignedLevel N)) _ _ (Quotient.out_eq' q))
  exact ⟨⟨r⁻¹*g,hh⟩,by exact mul_inv_cancel_left r g⟩

/-- The actual fine-level quotient has finite hyperbolic measure.
A finite union of translates of the closed full modular domain
meets every orbit; no boundary disjointness needs to be invented. -/
theorem area_finite (N : ℕ) (hN : 5 ≤ N) : IsFiniteMeasure (area N hN) := by
  letI : NeZero N := ⟨by omega⟩
  let Q := Modular ⧸ SignedLevel N
  letI : Fintype Q := Fintype.ofFinite Q
  let r : Q → Modular := Quotient.out
  let W : Set UpperHalfPlane :=
    ⋃ c : Q, (Matrix.SpecialLinearGroup.mapGL ℝ ((r c)⁻¹) : GL (Fin 2) ℝ) • ModularGroup.fd
  have hhit (z : UpperHalfPlane) : ∃ g : image N, z ∈ g • W := by
    obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd z
    obtain ⟨h,hh⟩ := coset_decompose N g
    let c : Q := QuotientGroup.mk g
    let h' : image N := ⟨positiveMatrix N h⁻¹,⟨h⁻¹,rfl⟩⟩
    let y := (r c)⁻¹ • (g • z)
    have hy : y ∈ W := Set.mem_iUnion_of_mem c
      ⟨g • z,hg,by rfl⟩
    have hact : h' • y = z := by
      change h.val⁻¹ • ((r c)⁻¹ • (g • z)) = z
      have he : r c * h.val = g := hh
      rw [←he,mul_smul,inv_smul_smul,inv_smul_smul]
    exact ⟨h',⟨y,hy,hact⟩⟩
  refine ⟨(area_univ_le_of_cover N hN W hhit).trans_lt ?_⟩
  change volume (⋃ c : Q, (Matrix.SpecialLinearGroup.mapGL ℝ ((r c)⁻¹) : GL (Fin 2) ℝ) •
    ModularGroup.fd) < ∞
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.2
  intro c _
  rw [measure_smul]
  exact standard_fd_finite

/-- The actual cross Petersson integrand is integrable on the same
quotient measure used in the same-center minor and metric. -/
theorem cross_integrable (N : ℕ) (hN : 5 ≤ N) (f g : Form N) :
    Integrable (cross f g) (area N hN) := by
  letI : NeZero N := ⟨by omega⟩
  letI : (subgroup N).IsArithmetic :=
    Subgroup.isArithmetic_iff_finiteIndex.mpr (inferInstance : (SignedLevel N).FiniteIndex)
  letI : IsFiniteMeasure (area N hN) := area_finite N hN
  obtain ⟨B,hB⟩ := CuspFormClass.petersson_bounded_left 2 (subgroup N) f g
  have hmeas : Measurable (cross f g) := by
    apply measurable_from_quotient.mpr
    change Measurable (UpperHalfPlane.petersson 2 (fun z => f z) (fun z => g z))
    exact (UpperHalfPlane.petersson_continuous _ (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).measurable
  refine (integrable_const B).mono' hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun q => by
    obtain ⟨τ,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
    exact hB τ)

end SelectedGammaOneFinitePetersson318

#print axioms SelectedGammaOneFinitePetersson318.area_finite
#print axioms SelectedGammaOneFinitePetersson318.cross_integrable
