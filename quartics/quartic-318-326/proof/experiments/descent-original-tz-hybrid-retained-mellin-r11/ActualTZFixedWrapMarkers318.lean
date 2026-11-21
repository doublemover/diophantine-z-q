module
public import ActualTZLiteralTerminalLift318
import all ActualTZLiteralTerminalLift318
public section
noncomputable section
namespace ActualTZFixedWrapMarkers318
open ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318
open scoped BigOperators

variable {σ : Type*}

@[expose] def Varies (P : MvPolynomial σ ℤ) : Prop :=
  ∃ y z : σ→ℤ,MvPolynomial.eval y P≠MvPolynomial.eval z P

/-- One nonconstant monomial, without needing to double a
diagonal coefficient or use a mod-2 finite-difference probe. -/
theorem varies_coeff (P : MvPolynomial σ ℤ) (h : Varies P) :
    ∃ u : σ→₀ℕ,u≠0 ∧ P.coeff u≠0 := by
  classical
  obtain ⟨y,z,hy⟩ := h
  by_contra hn
  have hC : P=MvPolynomial.C (P.coeff 0) := by
    ext u
    by_cases hu : u=0
    · subst u
      rw [MvPolynomial.coeff_zero_C]
    · rw [MvPolynomial.coeff_C_of_ne_zero hu]
      by_contra he
      exact hn ⟨u,hu,he⟩
  apply hy
  rw [hC,MvPolynomial.eval_C,MvPolynomial.eval_C]

variable {m a b j : ℕ}

theorem physical_coeff (S : Terminal m a b) (W n : ℕ) (r r' : ℤ) (u v : Site a b j)
    (z : Axis m a j→₀ℕ) (hz : z≠0) :
    (physicalP S W n r r' u v).coeff z=(W:ℤ)*(siteP S u-siteP S v).coeff z := by
  simp only [physicalP,MvPolynomial.coeff_add,MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul,MvPolynomial.coeff_C_of_ne_zero hz,sub_zero,add_zero]

/-- Fixed marker chosen once for a pair, uniform over all actual
wraps and original wheel translates. -/
theorem fixed_wrap_marker (S : Terminal m a b) (W : ℕ) (hW : 0<W) (u v : Site a b j)
    (hUV : Varies (siteP S u-siteP S v)) :
    ∃ z : Axis m a j→₀ℕ,∃ c : ℤ,z≠0 ∧ c≠0 ∧
      ∀ n (r r' : ℤ),(physicalP S W n r r' u v).coeff z=c := by
  obtain ⟨z,hz,hz'⟩ := varies_coeff _ hUV
  have hw : (W:ℤ)≠0 := by exact_mod_cast hW.ne'
  exact ⟨z,(W:ℤ)*(siteP S u-siteP S v).coeff z,hz,mul_ne_zero hw hz',
    fun n r r' => physical_coeff S W n r r' u v z hz⟩

end ActualTZFixedWrapMarkers318
