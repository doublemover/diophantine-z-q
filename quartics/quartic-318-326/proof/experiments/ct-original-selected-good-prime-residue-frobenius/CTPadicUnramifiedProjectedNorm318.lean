module
public import CTUnramifiedResidueBasis318
public import CTPadicUnitNormHensel318
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Valuation.Integers
public section
noncomputable section

namespace CTPadicUnramifiedProjectedNorm318

open IsLocalRing CTUnramifiedResidueBasis318
open scoped nonZeroDivisors BigOperators

section Integral

variable {p : ℕ} [Fact p.Prime]
variable {S ι : Type*} [CommRing S] [Algebra ℤ_[p] S] [IsLocalRing S]
  [IsLocalHom (algebraMap ℤ_[p] S)] [Fintype ι] [DecidableEq ι]

/-- The prior Hensel proof is applied to the literal residue of the
chosen local ring. Its matrix square follows from the SAME integral
basis, reduced by the extended maximal-ideal equality, not supplied
as a separate arithmetic hypothesis. -/
theorem unit_norm_surj_of_integral_basis
    (b : Basis ι ℤ_[p] S)
    (hI : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S) = maximalIdeal S) :
    Function.Surjective (Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p])) := by
  let k := ResidueField ℤ_[p]
  let l := ResidueField S
  let c := residueBasis hI b
  letI : Fintype k := Fintype.ofEquiv (ZMod p) PadicInt.residueField.symm.toEquiv
  letI : Fintype l := Fintype.ofEquiv (ι → k) c.equivFun.symm.toEquiv
  let r : ℤ_[p] →+* k := residue ℤ_[p]
  let s : S →+* l := residue S
  have hm (x : S) : (Algebra.leftMulMatrix b x).map r = Algebra.leftMulMatrix c (s x) := by
    ext i j
    simp only [Matrix.map_apply,Algebra.leftMulMatrix_eq_repr_mul]
    change residue ℤ_[p] (b.repr (x * b j) i) =
      c.repr (residue S x * c j) i
    rw [show c j = residue S (b j) from residueBasis_apply hI b j,
      ← map_mul,show c.repr (residue S (x * b j)) i =
        residue ℤ_[p] (b.repr (x * b j) i) from residueBasis_repr hI b (x*b j) i]
  have hZ (x : ℤ_[p]) : r x = 0 ↔ ‖x‖ < 1 :=
    (residue_eq_zero_iff x).trans PadicInt.not_isUnit_iff
  have hSU : Function.Surjective (Units.map s.toMonoidHom) := by
    intro a
    obtain ⟨x,hx⟩ := (residue_surjective (R := S)) (a : l)
    have hu : IsUnit x := (residue_ne_zero_iff_isUnit x).1 (fun h => a.ne_zero (hx.symm.trans h))
    refine ⟨hu.unit,Units.ext ?_⟩
    change residue S (hu.unit : S) = (a : l)
    rw [hu.unit_spec,hx]
  apply CTPadicUnitNormHensel318.unit_norm_surj_of_residue_comparisons
    b r s hZ (residue_surjective (R := S)) hSU
  · intro x
    rw [Algebra.norm_eq_matrix_det b,Algebra.norm_eq_matrix_det c,RingHom.map_det]
    exact congrArg Matrix.det (hm x)
  · intro x
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace c,← hm]
    simp [Matrix.trace,map_sum,Matrix.map_apply]

/-- With the actual finite local formally unramified structure, no
independent residue-field or multiplication-matrix witness is needed. -/
theorem unit_norm_surj_of_unramified_basis
    [EssFiniteType ℤ_[p] S] [Algebra.FormallyUnramified ℤ_[p] S]
    (b : Basis ι ℤ_[p] S) :
    Function.Surjective (Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p])) :=
  unit_norm_surj_of_integral_basis b maximalIdeal_map_of_unramified

end Integral

section Projected

variable {p : ℕ} [Fact p.Prime]
variable {S L ι : Type*} [CommRing S] [IsDomain S] [Field L]
  [Algebra ℤ_[p] S] [FaithfulSMul ℤ_[p] S] [Algebra S L] [Algebra ℤ_[p] L]
  [Algebra ℚ_[p] L] [IsScalarTower ℤ_[p] S L] [IsScalarTower ℤ_[p] ℚ_[p] L]
  [IsFractionRing S L] [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
  [Fintype ι] [DecidableEq ι]

/-- Exact fraction-field matrix on the localization of the SAME
integral basis. The base localization is the native Q_p. -/
theorem same_integral_fraction_matrix (b : Basis ι ℤ_[p] S) (x : S)
    [IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[p])) L] :
    (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (Algebra.leftMulMatrix b x) =
      Algebra.leftMulMatrix (b.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) L)
        (algebraMap S L x) :=
  Algebra.map_leftMulMatrix_localization ℤ_[p] (nonZeroDivisors ℤ_[p]) b x

/-- The actual multiplicative Galois norm in the selected fraction
field, not a norm on a residue or a substitute extension. -/
theorem actual_unit_galois_product_from_integral_norm
    (b : Basis ι ℤ_[p] S)
    (hN : Function.Surjective (Units.map (Algebra.norm ℤ_[p] : S →* ℤ_[p])))
    (a : ℤ_[p]ˣ) :
    ∃ w : Sˣ, (∏ σ : L ≃ₐ[ℚ_[p]] L, σ (algebraMap S L (w : S))) =
      algebraMap ℤ_[p] L (a : ℤ_[p]) := by
  letI : Module.Free ℤ_[p] S := Module.Free.of_basis b
  letI : Module.Finite ℤ_[p] S := Module.Finite.of_basis b
  letI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[p])) L := inferInstance
  obtain ⟨w,hw⟩ := hN a
  have hn : Algebra.norm ℤ_[p] (w : S) = (a : ℤ_[p]) := congrArg Units.val hw
  refine ⟨w,?_⟩
  rw [← Algebra.norm_eq_prod_automorphisms,Algebra.norm_localization ℤ_[p] (nonZeroDivisors ℤ_[p]),
    hn,IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L]

/-- End-to-end integral-to-Galois norm lift for the selected unramified
local ring, once its actual fraction-field and unramified structures
are supplied. No extra invariant or norm surjectivity premise. -/
theorem actual_unramified_unit_galois_product
    [IsLocalRing S] [IsLocalHom (algebraMap ℤ_[p] S)]
    [EssFiniteType ℤ_[p] S] [Algebra.FormallyUnramified ℤ_[p] S]
    (b : Basis ι ℤ_[p] S) (a : ℤ_[p]ˣ) :
    ∃ w : Sˣ, (∏ σ : L ≃ₐ[ℚ_[p]] L, σ (algebraMap S L (w : S))) =
      algebraMap ℤ_[p] L (a : ℤ_[p]) :=
  actual_unit_galois_product_from_integral_norm b (unit_norm_surj_of_unramified_basis b) a

/-- A Galois-fixed integral unit actually comes from a base unit,
not merely from a nonzero base-field element. -/
theorem fixed_integral_unit_base_preimage {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (hv : v.Integers S)
    (hValueOne : ∀ x : ℚ_[p], v (algebraMap ℚ_[p] L x) = 1 ↔ ‖x‖ = 1)
    (u : Sˣ)
    (hu : ∀ σ : L ≃ₐ[ℚ_[p]] L, σ (algebraMap S L (u : S)) = algebraMap S L (u : S)) :
    ∃ a : ℤ_[p]ˣ, algebraMap ℤ_[p] L (a : ℤ_[p]) = algebraMap S L (u : S) := by
  obtain ⟨x,hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := ℚ_[p]) (E := L) (algebraMap S L (u : S))).2 hu
  have h : ‖x‖ = 1 := (hValueOne x).1 (by rw [hx]; exact hv.valuation_unit u)
  let a := PadicInt.mkUnits h
  have ha : algebraMap ℤ_[p] ℚ_[p] (a : ℤ_[p]) = x := PadicInt.mkUnits_eq h
  exact ⟨a,by rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L,ha,hx]⟩

/-- Exact target of the projected norm-on-fixed-elements step for the
actual unramified layer. Galois invariance is for the same embedded unit. -/
theorem actual_unramified_norm_onto_fixed_units
    [IsLocalRing S] [IsLocalHom (algebraMap ℤ_[p] S)]
    [EssFiniteType ℤ_[p] S] [Algebra.FormallyUnramified ℤ_[p] S]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (b : Basis ι ℤ_[p] S) (v : Valuation L Γ) (hv : v.Integers S)
    (hValueOne : ∀ x : ℚ_[p], v (algebraMap ℚ_[p] L x) = 1 ↔ ‖x‖ = 1)
    (u : Sˣ)
    (hu : ∀ σ : L ≃ₐ[ℚ_[p]] L, σ (algebraMap S L (u : S)) = algebraMap S L (u : S)) :
    ∃ w : Sˣ, (∏ σ : L ≃ₐ[ℚ_[p]] L, σ (algebraMap S L (w : S))) = algebraMap S L (u : S) := by
  obtain ⟨a,ha⟩ := fixed_integral_unit_base_preimage v hv hValueOne u hu
  obtain ⟨w,hw⟩ := actual_unramified_unit_galois_product b a
  exact ⟨w,hw.trans ha⟩

end Projected
end CTPadicUnramifiedProjectedNorm318
