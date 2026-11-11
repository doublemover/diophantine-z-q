module
public import PELOriginalMetricSmoothCoefficient318
public section
noncomputable section
namespace PELOriginalIntegralDualLattice318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318
open PELOriginalPeriodLattice318 PELOriginalMetricSmoothCoefficient318
variable (τ:ℂ)(hτ:0<τ.im)
abbrev L:=PELOriginalPeriodLattice318.lattice τ hτ
lemma basis_mem(i:Fin 4):basis τ hτ i∈L τ hτ:=
  Submodule.subset_span ⟨i,rfl⟩

/-- A real-linear functional is determined on the ENTIRE original
period carrier by the original full integral lattice, not a sublattice. -/
lemma linear_ext_lattice{f g:ComplexVectors→ₗ[ℝ]ℝ}
    (h:∀l:L τ hτ,f l.val=g l.val):f=g:=by
  apply (basis τ hτ).ext
  intro i
  exact h ⟨basis τ hτ i,basis_mem τ hτ i⟩

@[expose] def integerPairing(δ:ComplexVectors)
    (hi:∀l:L τ hτ,∃n:ℤ,riemann τ hτ δ l.val=(n:ℝ))(l:L τ hτ):ℤ:=
  (hi l).choose
lemma integerPairing_value(δ:ComplexVectors)
    (hi:∀l:L τ hτ,∃n:ℤ,riemann τ hτ δ l.val=(n:ℝ))(l:L τ hτ):
    (integerPairing τ hτ δ hi l:ℝ)=riemann τ hτ δ l.val:=
  (hi l).choose_spec.symm
@[expose] def integralFunctional(δ:ComplexVectors)
    (hi:∀l:L τ hτ,∃n:ℤ,riemann τ hτ δ l.val=(n:ℝ)):L τ hτ→ₗ[ℤ]ℤ where
  toFun:=integerPairing τ hτ δ hi
  map_add' l m:=by
    apply Int.cast_injective (R:=ℝ)
    rw [Int.cast_add,integerPairing_value,integerPairing_value,integerPairing_value]
    exact add_right τ hτ δ l.val m.val
  map_smul' n l:=by
    apply Int.cast_injective (R:=ℝ)
    simp only [smul_eq_mul,Int.cast_mul]
    rw [integerPairing_value,integerPairing_value]
    change riemann τ hτ δ (n • l.val)=(n:ℝ)*riemann τ hτ δ l.val
    rw [←Int.cast_smul_eq_zsmul ℝ]
    exact smul_right τ hτ (n:ℝ) δ l.val

/-- Principal perfectness plus the ACTUAL full real lattice basis
identifies its integral symplectic dual with the SAME original lattice.
The proof does not weaken integral pairing to rational pairing. -/
theorem mem_of_integral_pairings(δ:ComplexVectors)
    (hi:∀l:L τ hτ,∃n:ℤ,riemann τ hτ δ l.val=(n:ℝ)):
    δ∈L τ hτ:=by
  obtain ⟨x,hx,hunique⟩:=perfect τ hτ (integralFunctional τ hτ δ hi)
  have he:secondLinear τ hτ δ=secondLinear τ hτ x.val:=by
    apply linear_ext_lattice τ hτ
    intro l
    change riemann τ hτ δ l.val=riemann τ hτ x.val l.val
    rw [integralRiemann_value,hx]
    exact (integerPairing_value τ hτ δ hi l).symm
  have hall:∀w,riemann τ hτ δ w=riemann τ hτ x.val w:=
    fun w=>congrArg (fun f:ComplexVectors→ₗ[ℝ]ℝ=>f w) he
  have hz:δ-x.val=0:=by
    by_contra hn
    have hp:=positive τ hτ (δ-x.val) hn
    have heq:riemann τ hτ (δ-x.val) (Complex.I • (δ-x.val))=0:=by
      change riemann τ hτ (δ+(-x.val)) (Complex.I • (δ-x.val))=0
      rw [add_left]
      have hneg:riemann τ hτ (-x.val) (Complex.I • (δ-x.val))=
          -riemann τ hτ x.val (Complex.I • (δ-x.val)):=by
        simpa only [neg_one_smul,neg_one_mul] using
          smul_left τ hτ (-1:ℝ) x.val (Complex.I • (δ-x.val))
      rw [hneg,hall]
      ring
    rw [heq] at hp
    exact (lt_irrefl 0) hp
  rw [sub_eq_zero.mp hz]
  exact x.property
end PELOriginalIntegralDualLattice318
