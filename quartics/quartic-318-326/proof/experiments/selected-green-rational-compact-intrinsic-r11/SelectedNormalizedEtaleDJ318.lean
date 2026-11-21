module
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.AdjoinRoot
public section
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

namespace SelectedNormalizedEtaleDJ318

section EtaleTransport
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [Algebra.FormallyEtale R S]

/-- Transport the genuine frame across the étale algebra map. -/
@[expose] def etaleFrame (f : KaehlerDifferential K R ≃ₗ[R] R) :
    KaehlerDifferential K S ≃ₗ[S] S :=
  (tensorKaehlerEquivOfFormallyEtale K R S).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) f ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R S S

/-- Exact normalization on all pullbacks from the base, not just equality
of dimensions or an arbitrary unit multiple of the chosen generator. -/
theorem etaleFrame_D (f : KaehlerDifferential K R ≃ₗ[R] R) (r : R) :
    etaleFrame f (D K S (algebraMap R S r)) = algebraMap R S (f (D K R r)) := by
  simp only [etaleFrame,LinearEquiv.trans_apply,tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def,mul_one]

end EtaleTransport

section ScalarExtension
variable {K S F : Type*} [CommRing K] [CommRing S] [CommRing F]
variable [Algebra K S] [Algebra K F]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Genuine scalar extension of the same frame, used at Q and C. -/
@[expose] def tensorFrame (f : KaehlerDifferential K S ≃ₗ[S] S) :
    KaehlerDifferential F (F ⊗[K] S) ≃ₗ[F ⊗[K] S] F ⊗[K] S :=
  (tensorKaehlerEquiv K F S (F ⊗[K] S)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) f ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid S _ _

theorem tensorFrame_normalized (f : KaehlerDifferential K S ≃ₗ[S] S) (j : S)
    (hj : f (D K S j) = 1) :
    tensorFrame (F := F) f (D F (F ⊗[K] S) ((1 : F) ⊗ₜ[K] j)) = 1 := by
  simp only [tensorFrame,LinearEquiv.trans_apply,tensorKaehlerEquiv_symm_D_tmul,map_one,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,hj,
    TensorProduct.AlgebraTensorModule.rid_tmul,one_smul]

end ScalarExtension

section Coefficient
variable {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]

/-- The coefficient belongs to the actual ring of regular functions, not
a separately chosen value or a coefficient in the fraction field only. -/
theorem coefficient_spec (f : KaehlerDifferential K S ≃ₗ[S] S) (j : S)
    (hj : f (D K S j) = 1) (ω : KaehlerDifferential K S) :
    ω = (f ω) • D K S j := by
  apply f.injective
  rw [map_smul,hj,smul_eq_mul,mul_one]

theorem coefficient_iff (f : KaehlerDifferential K S ≃ₗ[S] S) (j : S)
    (hj : f (D K S j) = 1) (ω : KaehlerDifferential K S) (a : S) :
    ω = a • D K S j ↔ f ω = a := by
  constructor
  · intro h
    rw [h,map_smul,hj,smul_eq_mul,mul_one]
  · intro h
    exact (coefficient_spec f j hj ω).trans (congrArg (fun b : S => b • D K S j) h)

end Coefficient

section MonicRoot
variable {R : Type*} [CommRing R]

/-- The precise derivative is a unit on the genuine monic root algebra:
the derivative localization in the standard étale pair is then trivial. -/
theorem etale_of_derivative (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (AdjoinRoot.mk p p.derivative)) : Algebra.Etale R (AdjoinRoot p) := by
  let P : StandardEtalePair R :=
    { f := p, monic_f := hp, g := p.derivative, cond := ⟨1,0,1,by simp⟩ }
  let E := P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot p)
      (Localization.Away (AdjoinRoot.mk p p.derivative)) _ hu).symm.restrictScalars R)
  exact Algebra.Etale.of_equiv E

end MonicRoot

section Implicit
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K S]

/-- Differentiate both the genuine coefficient map and the root; no
coefficients of P have silently been treated as constants. -/
theorem derive_eval₂ (δ : Derivation K S S) (α : R →+* S) (x : S) (p : R[X]) :
    δ (p.eval₂ α x) = p.derivative.eval₂ α x * δ x +
      p.sum (fun n a => δ (α a) * x^n) := by
  have hder : p.derivative.eval₂ α x =
      p.sum (fun n a => α a * (n : S) * x^(n-1)) := by
    rw [Polynomial.derivative_apply,Polynomial.eval₂_sum]
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,
      Polynomial.eval₂_X,map_mul,map_natCast,Polynomial.eval₂_natCast]
  rw [hder,Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum_def,map_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [δ.leibniz,δ.leibniz_pow,nsmul_eq_mul,smul_eq_mul]
  ring

theorem implicit_relation (δ : Derivation K S S) (α : R →+* S) (x : S) (p : R[X])
    (hx : p.eval₂ α x = 0) :
    p.derivative.eval₂ α x * δ x = -p.sum (fun n a => δ (α a) * x^n) := by
  have h := derive_eval₂ δ α x p
  rw [hx,map_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Solve the signed implicit relation using this actual derivative unit. -/
theorem implicit_solve (δ : Derivation K S S) (α : R →+* S) (x : S) (p : R[X])
    (hx : p.eval₂ α x = 0) (hu : IsUnit (p.derivative.eval₂ α x)) :
    δ x = (↑hu.unit⁻¹ : S) * (-p.sum (fun n a => δ (α a) * x^n)) := by
  have hUnit : (↑hu.unit⁻¹ : S) * p.derivative.eval₂ α x = 1 := by
    calc
      _ = (↑hu.unit⁻¹:S)*(hu.unit:S) :=
        congrArg (fun z:S => (↑hu.unit⁻¹:S)*z) hu.unit_spec.symm
      _ = 1 := Units.inv_mul _
  calc
    δ x = (↑hu.unit⁻¹ : S) * (p.derivative.eval₂ α x * δ x) := by
      rw [← mul_assoc,hUnit,one_mul]
    _ = _ := by rw [implicit_relation δ α x p hx]

end Implicit
end SelectedNormalizedEtaleDJ318

#print axioms SelectedNormalizedEtaleDJ318.etaleFrame_D
#print axioms SelectedNormalizedEtaleDJ318.tensorFrame_normalized
#print axioms SelectedNormalizedEtaleDJ318.implicit_solve
