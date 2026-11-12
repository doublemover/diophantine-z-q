module
public import ConcreteG8Domain
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic
public section
namespace ConcretePadic318
open ConcreteG8Domain
open scoped QuadraticAlgebra
variable (p : ℕ) [Fact p.Prime]

/-- The actual p-adic realization at a chosen square root of two. -/
noncomputable def embedding (rho : ℚ_[p]) (hr : rho^2=2) : K →ₐ[ℚ] ℚ_[p] :=
  QuadraticAlgebra.lift ⟨rho,by simpa [pow_two,Algebra.smul_def] using hr⟩

theorem embedding_pair (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    embedding p rho hr (pair a b)=(a:ℚ_[p])+(b:ℚ_[p])*rho := by
  simp [embedding,QuadraticAlgebra.lift_apply_apply,pair,Algebra.smul_def]

noncomputable def place (rho : ℚ_[p]) (hr : rho^2=2) : AddValuation K (WithTop ℤ) :=
  Padic.addValuation.comap (embedding p rho hr).toRingHom

noncomputable def rationalPlace : AddValuation ℚ (WithTop ℤ) :=
  Padic.addValuation.comap (algebraMap ℚ ℚ_[p])

theorem place_pair (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    place p rho hr (pair a b)=Padic.addValuation ((a:ℚ_[p])+(b:ℚ_[p])*rho) := by
  change Padic.addValuation (embedding p rho hr (pair a b))=_
  rw [embedding_pair]

theorem place_rational (rho : ℚ_[p]) (hr : rho^2=2) (q : ℚ) :
    place p rho hr (pair q 0)=rationalPlace p q := by
  rw [place_pair]
  change Padic.addValuation ((q:ℚ_[p])+(0:ℚ_[p])*rho)=Padic.addValuation (q:ℚ_[p])
  simp

theorem rational_value (q : ℚ) (hq : q≠0) :
    rationalPlace p q=(padicValRat p q : WithTop ℤ) := by
  change Padic.addValuation (q:ℚ_[p])=_
  rw [Padic.addValuation.apply (by exact_mod_cast hq),Padic.valuation_ratCast]

theorem rational_nat_unit (n : ℕ) (hn : ¬p∣n) :
    rationalPlace p (n:ℚ)=0 := by
  have hn0 : n≠0 := by intro h; subst n; exact hn (dvd_zero p)
  rw [rational_value p _ (by exact_mod_cast hn0),padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hn]
  rfl

theorem negative_root (rho : ℚ_[p]) (hr : rho^2=2) : (-rho)^2=2 := by
  simpa using hr

theorem conjugate_embedding (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    embedding p (-rho) (negative_root p rho hr) (pair a b)=
      embedding p rho hr (pair a (-b)) := by
  simp [embedding_pair]

theorem norm_identity (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    embedding p rho hr (pair a b)*embedding p (-rho) (negative_root p rho hr) (pair a b)=
      ((a^2-2*b^2:ℚ):ℚ_[p]) := by
  simp only [embedding_pair,Rat.cast_sub,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat]
  linear_combination -(b:ℚ_[p])^2*hr

theorem norm_valuation (rho : ℚ_[p]) (hr : rho^2=2) (a b : ℚ) :
    place p rho hr (pair a b)+place p (-rho) (negative_root p rho hr) (pair a b)=
      rationalPlace p (a^2-2*b^2) := by
  change Padic.addValuation (embedding p rho hr (pair a b))+
    Padic.addValuation (embedding p (-rho) (negative_root p rho hr) (pair a b))=_
  rw [←Padic.addValuation.map_mul,norm_identity]
  rfl

end ConcretePadic318
