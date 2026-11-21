module
public import GammaOneAtlas318
public import Mathlib.NumberTheory.ModularForms.Petersson
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic
public section
noncomputable section
open scoped MatrixGroups ComplexConjugate BigOperators
open MeasureTheory UpperHalfPlane Matrix GammaOneAtlas318 GammaOneFiber318
open PeterssonQuotient318 DerivativeCocycle318

namespace SelectedWeightTwoPetersson318

/-- The actual same-level determinant-one subgroup as a subgroup of GL₂(ℝ),
rather than the positive-matrix image used for the already formed quotient. -/
abbrev subgroup (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

abbrev Form (N : ℕ) := CuspForm (subgroup N) 2

private theorem group_mem {N : ℕ} {g : G} (hg : g ∈ image N) :
    (g : GL (Fin 2) ℝ) ∈ subgroup N := by
  obtain ⟨γ,rfl⟩ := hg
  exact ⟨γ.val,γ.property,rfl⟩

private theorem period_det {N : ℕ} {g : G} (hg : g ∈ image N) :
    (g : GL (Fin 2) ℝ).val.det = 1 := by
  obtain ⟨γ,rfl⟩ := hg
  exact GammaOneFree318.realMatrix_det γ.val

/-- Genuine linear differential descent on the given level quotient.
It uses one power of the complex derivative, not the quadratic-differential
cocycle from the D=210 comparison. -/
theorem differential_pullback {N : ℕ} (f : Form N) (g : image N) (τ : UpperHalfPlane) :
    f (g • τ) * derivative (g : G) τ = f τ := by
  change f (((g : G) : GL (Fin 2) ℝ) • τ) * derivative (g : G) τ = f τ
  rw [SlashInvariantForm.slash_action_eqn'' f (group_mem (N:=N) g.property) τ,
    derivative, period_det (N:=N) g.property, Complex.ofReal_one, zpow_ofNat]
  field_simp [UpperHalfPlane.denom_ne_zero _ _]

/-- The cross-energy scalar descends to the actual orbit quotient. It is
complex Hermitian and retains all off-diagonal coefficients of one basis. -/
@[expose] def cross {N : ℕ} (f h : Form N) : Base (image N) → ℂ :=
  Quotient.lift (UpperHalfPlane.petersson 2 f h) (by
    intro a b hab
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hab
    change (g : G) • b = a at hg
    rw [← hg]
    exact SlashInvariantFormClass.petersson_smul (f := f) (f' := h)
      (τ := b) (group_mem (N:=N) g.property))

theorem cross_projection {N : ℕ} (f h : Form N) (τ : UpperHalfPlane) :
    cross f h (quotientMap N τ) = conj (f τ) * h τ * ((τ.im : ℂ)^2) := by
  change UpperHalfPlane.petersson 2 f h τ = _
  simp only [UpperHalfPlane.petersson,zpow_ofNat]

/-- The actual hyperbolic period-chart density multiplying the Petersson
integrand gives the ordinary mixed energy density, exactly. In the chart
weight two introduces no factor 2, π, area index or level correction. -/
theorem period_density {N : ℕ} (f h : Form N) (τ : UpperHalfPlane) :
    cross f h (quotientMap N τ) * ((τ.im : ℂ)^2)⁻¹ = conj (f τ) * h τ := by
  have hy : (τ.im : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  rw [cross_projection, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hy), mul_one]

/-- The diagonal real density for a holomorphic one-form. This is the
chart density used by the ordinary Lebesgue-area change of variables. -/
theorem period_energy {N : ℕ} (f : Form N) (τ : UpperHalfPlane) :
    (cross f f (quotientMap N τ)).re / τ.im^2 = ‖f τ‖^2 := by
  have h := congrArg Complex.re (period_density f f τ)
  rw [← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re,Complex.normSq_eq_norm_sq,← div_eq_mul_inv] at h
  exact h

private def eval {N : ℕ} (τ : UpperHalfPlane) : Form N →ₗ[ℂ] ℂ where
  toFun f := f τ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Combine the *same* actual weight-two cusp forms before evaluating
on any sheet. The coefficients use the Euclidean, not maximum, norm. -/
@[expose] def combination {N g : ℕ} (b : Fin g → Form N)
    (x : EuclideanSpace ℂ (Fin g)) : Form N := ∑ j, x j • b j

theorem combination_apply {N g : ℕ} (b : Fin g → Form N)
    (x : EuclideanSpace ℂ (Fin g)) (τ : UpperHalfPlane) :
    combination b x τ = ∑ j, x j * b j τ := by
  change eval τ (∑ j, x j • b j) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  rfl

theorem cross_combination {N g : ℕ} (b : Fin g → Form N)
    (x : EuclideanSpace ℂ (Fin g)) (q : Base (image N)) :
    cross (combination b x) (combination b x) q =
      ∑ i, ∑ j, (conj (x i) * x j) * cross (b i) (b j) q := by
  obtain ⟨τ,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
  simp only [cross_projection,combination_apply,map_sum,map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- All combinations are normalized by the ordinary pairwise Gram matrix of
one *fixed* family on this actual quotient. In particular this statement
does not take unit-combination energy or a row-wise energy as input.
The geometric measure still needs to be identified with the Hodge metric. -/
theorem gram_energy {N g : ℕ} [MeasurableSpace (Base (image N))]
    (μ : Measure (Base (image N))) (b : Fin g → Form N)
    (hI : ∀ i j, Integrable (cross (b i) (b j)) μ)
    (hG : ∀ i j, (∫ q, cross (b i) (b j) q ∂μ) = if i = j then 1 else 0)
    (x : EuclideanSpace ℂ (Fin g)) :
    Integrable (cross (combination b x) (combination b x)) μ ∧
      (∫ q, cross (combination b x) (combination b x) q ∂μ) = (‖x‖^2 : ℝ) := by
  classical
  have hpair (i j : Fin g) :
      Integrable (fun q => (conj (x i) * x j) * cross (b i) (b j) q) μ := by
    exact (hI i j).const_mul _
  have hrow (i : Fin g) :
      Integrable (fun q => ∑ j, (conj (x i) * x j) * cross (b i) (b j) q) μ :=
    integrable_finsetSum _ (fun j _ => hpair i j)
  have heq : cross (combination b x) (combination b x) =
      fun q => ∑ i, ∑ j, (conj (x i) * x j) * cross (b i) (b j) q :=
    funext (cross_combination b x)
  rw [heq]
  constructor
  · exact integrable_finsetSum _ (fun i _ => hrow i)
  · have hdiag (i : Fin g) :
        (∫ q, ∑ j, (conj (x i) * x j) * cross (b i) (b j) q ∂μ) =
          conj (x i) * x i := by
      rw [integral_finsetSum _ (fun j _ => hpair i j)]
      simp_rw [integral_const_mul,hG]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    rw [integral_finsetSum _ (fun i _ => hrow i)]
    simp_rw [hdiag]
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_pow ‖x i‖ 2

theorem unit_energy {N g : ℕ} [MeasurableSpace (Base (image N))]
    (μ : Measure (Base (image N))) (b : Fin g → Form N)
    (hI : ∀ i j, Integrable (cross (b i) (b j)) μ)
    (hG : ∀ i j, (∫ q, cross (b i) (b j) q ∂μ) = if i = j then 1 else 0)
    (x : EuclideanSpace ℂ (Fin g)) (hx : ‖x‖ = 1) :
    (∫ q, cross (combination b x) (combination b x) q ∂μ) = 1 := by
  simpa only [hx,one_pow,Complex.ofReal_one] using (gram_energy μ b hI hG x).2

end SelectedWeightTwoPetersson318
#print axioms SelectedWeightTwoPetersson318.differential_pullback
#print axioms SelectedWeightTwoPetersson318.period_density
#print axioms SelectedWeightTwoPetersson318.gram_energy
