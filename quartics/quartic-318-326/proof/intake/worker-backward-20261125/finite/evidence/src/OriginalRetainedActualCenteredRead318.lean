module

public import OriginalRetainedComplexAffineEquation318
public import OriginalRetainedProjectiveAffinePoints318

@[expose] public section
noncomputable section

namespace OriginalRetainedActualCenteredRead318

open OriginalRetainedComplexAffineEquation318
open scoped Topology

variable {m : ℕ} (p : Fin m → Polynomials m) (g : coordinateQuotient p)
variable {B : Type} [CommRing B] [Algebra ℂ B] [Algebra (coordinateQuotient p) B]
variable [IsLocalization.Away g B]
variable (sc : (scalar p : ℂ →+* B)=algebraMap ℂ B)

def free (q : B →ₐ[ℂ] ℂ) (i : Fin 2) : ℂ := q (slot p (.inl i))
def aux (q : B →ₐ[ℂ] ℂ) (i : Fin m) : ℂ := q (slot p (.inr i))

include sc in
theorem read_polynomial (q : B →ₐ[ℂ] ℂ) :
    q.toRingHom.comp ((algebraMap (coordinateQuotient p) B).comp
      (Ideal.Quotient.mk (relationsIdeal p)))=eval (free p q) (aux p q) := by
  apply MvPolynomial.ringHom_ext'
  · change q.toRingHom.comp (scalar p)=_
    rw [sc]
    apply RingHom.ext
    intro t
    rw [RingHom.comp_apply]
    change q (algebraMap ℂ B t)=MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.C t)
    rw [q.commutes,Algebra.algebraMap_self,MvPolynomial.eval₂Hom_C]
  · rintro (i|i)
    · change free p q i=MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.X (.inl i))
      rw [MvPolynomial.eval₂Hom_X']
      rfl
    · change aux p q i=MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.X (.inr i))
      rw [MvPolynomial.eval₂Hom_X']
      rfl

include sc in
theorem read_equations (q : B →ₐ[ℂ] ℂ) (i : Fin m) :
    eval (free p q) (aux p q) (p i)=0 := by
  rw [←read_polynomial p sc q]
  have zero : Ideal.Quotient.mk (relationsIdeal p) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i))
  change q (algebraMap (coordinateQuotient p) B (Ideal.Quotient.mk (relationsIdeal p) (p i)))=0
  rw [zero,map_zero,map_zero]

include sc in
theorem read_quotient (q : B →ₐ[ℂ] ℂ) (b : coordinateQuotient p) :
    evalQ p (read_equations p sc q) b=q (algebraMap (coordinateQuotient p) B b) := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective (I:=relationsIdeal p) b
  rw [evalQ,Ideal.Quotient.lift_mk,←read_polynomial p sc q]
  rfl

include sc in
theorem read_denominator (q : B →ₐ[ℂ] ℂ) :
    evalQ p (read_equations p sc q) g≠0 := by
  rw [read_quotient p sc q]
  exact (IsUnit.map q.toRingHom
    (IsLocalization.Away.algebraMap_isUnit (R:=coordinateQuotient p) (S:=B) g)).ne_zero

include sc in
theorem read_ringHom (q : B →ₐ[ℂ] ℂ) :
    evalAt p g (read_equations p sc q) (read_denominator p g sc q)=q.toRingHom := by
  apply IsLocalization.ringHom_ext (R:=coordinateQuotient p) (S:=B) (Submonoid.powers g)
  ext b
  change evalAt p g (read_equations p sc q) (read_denominator p g sc q)
    (algebraMap (coordinateQuotient p) B b)=q (algebraMap (coordinateQuotient p) B b)
  rw [evalAt,IsLocalization.Away.lift_eq,read_quotient p sc q]

def asAlgHom {x : Fin 2 → ℂ} {y : Fin m → ℂ}
    (h : ∀ i, eval x y (p i)=0) (hu : evalQ p h g≠0) : B →ₐ[ℂ] ℂ :=
  { toRingHom := evalAt p g h hu
    commutes' := fun c => by
      have e := RingHom.congr_fun (scalar_read p g h hu) c
      simpa only [RingHom.comp_apply,RingHom.id_apply,sc] using e }

variable {W : Type} [TopologicalSpace W]
variable (x : W → Fin 2 → ℂ) (y : W → Fin m → ℂ)
variable (hx : Continuous x) (hy : Continuous y)
variable (h : ∀ w, ∀ i, eval (x w) (y w) (p i)=0)
variable (hu : ∀ w, evalQ p (h w) g≠0)

include hx hy in
/-- Actual R125 coefficients, not only the two free coordinates,
are continuous along the old centered polynomial branch. -/
theorem all_branch_evaluations_continuous (b : B) :
    Continuous (fun w => asAlgHom p g sc (h w) (hu w) b) := by
  have tuple : Continuous (fun w => Sum.elim (x w) (y w)) := by
    apply continuous_pi
    rintro (i|i)
    · exact (continuous_apply i).comp hx
    · exact (continuous_apply i).comp hy
  have cts (z : coordinateQuotient p) : Continuous (fun w => evalQ p (h w) z) := by
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective (I:=relationsIdeal p) z
    have equal : (fun w => evalQ p (h w) (Ideal.Quotient.mk (relationsIdeal p) f)) =
        fun w => MvPolynomial.aeval (Sum.elim (x w) (y w)) f := by
      funext w
      rw [evalQ,Ideal.Quotient.lift_mk]
      change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ f =
        MvPolynomial.eval₂Hom (algebraMap ℂ ℂ) _ f
      rw [Algebra.algebraMap_self]
    rw [equal]
    exact (OriginalRetainedProjectiveAffinePoints318.eval_continuous f).comp tuple
  obtain ⟨n,r,hr⟩ := IsLocalization.Away.surj (S:=B) (x:=g) b
  have equal : (fun w => asAlgHom p g sc (h w) (hu w) b) =
      fun w => evalQ p (h w) r/(evalQ p (h w) g)^n := by
    funext w
    let e : B→+*ℂ := evalAt p g (h w) (hu w)
    have er (q : coordinateQuotient p) :
        e (algebraMap (coordinateQuotient p) B q)=evalQ p (h w) q :=
      IsLocalization.Away.lift_eq g (isUnit_iff_ne_zero.2 (hu w)) q
    have eq := congrArg e hr
    rw [map_mul,map_pow,er,er] at eq
    change e b=_
    exact (eq_div_iff (pow_ne_zero n (hu w))).2 eq
  rw [equal]
  exact (cts r).div₀ ((cts g).pow n) (fun w => pow_ne_zero n (hu w))

end OriginalRetainedActualCenteredRead318
