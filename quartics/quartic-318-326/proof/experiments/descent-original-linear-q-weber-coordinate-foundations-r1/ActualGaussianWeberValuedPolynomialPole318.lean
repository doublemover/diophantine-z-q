module
public import ActualGaussianWeberOrdinarySlope318
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public section
noncomputable section

namespace ActualGaussianWeberValuedPolynomialPole318

open IsLocalRing Polynomial
open ActualGaussianWeberOrdinarySlope318

variable {k F : Type*} [Field k] [Field F] (V : ValuationSubring F) (c : k →+* V)

/-- Coefficients are embedded in the actual valuation ring. Their
induced residue map is injective because the coefficient ring is a field. -/
private theorem inverse_small {x : F} (hx : x ∉ V) :
    ∃ z : V, V.subtype z=x⁻¹ ∧ residue V z=0 := by
  let z : V := ⟨x⁻¹,(V.mem_or_inv_mem x).resolve_left hx⟩
  have h : (z:F) ∈ V.nonunits := by
    change x⁻¹ ∈ V.nonunits
    exact (V.inv_mem_nonunits_iff).mpr (Or.inr hx)
  exact ⟨z,rfl,(residue_eq_zero_iff z).mpr ((V.coe_mem_nonunits_iff).mp h)⟩

private theorem reverse_residue (P : k[X]) (z : V) (hz : residue V z=0) :
    residue V (P.reverse.eval₂ c z)=residue V (c P.leadingCoeff) := by
  rw [hom_eval₂,hz,eval₂_at_zero,coeff_zero_reverse,RingHom.comp_apply]

private theorem reverse_residue_ne {P : k[X]} (hP : P≠0) (z : V) (hz : residue V z=0) :
    residue V (P.reverse.eval₂ c z)≠0 := by
  rw [reverse_residue V c P z hz]
  let m := (residue V).comp c
  change m P.leadingCoeff≠0
  intro h
  exact (leadingCoeff_ne_zero.mpr hP) (m.injective (h.trans (map_zero m).symm))

private theorem reverse_eval (P : k[X]) {x : F} (hx : x≠0) (z : V)
    (hz : V.subtype z=x⁻¹) :
    V.subtype (P.reverse.eval₂ c z)*x^P.natDegree=P.eval₂ (V.subtype.comp c) x := by
  letI := invertibleOfNonzero hx
  rw [hom_eval₂,hz]
  simpa only [invOf_eq_inv] using eval₂_reverse_mul_pow (V.subtype.comp c) x P

/-- A nonintegral abscissa gives an injective polynomial evaluation.
The reversed leading coefficient is nonzero in the exact residue field. -/
theorem evaluation_at_pole_injective {x : F} (hx : x ∉ V) :
    Function.Injective (eval₂RingHom (V.subtype.comp c) x) := by
  have hx₀ : x≠0 := fun h => hx (h.symm ▸ V.zero_mem)
  obtain ⟨z,hz,hzr⟩ := inverse_small V hx
  let e := eval₂RingHom (V.subtype.comp c) x
  have hZero (P : k[X]) (he : e P=0) : P=0 := by
    by_contra hP
    have hprod := (reverse_eval V c P hx₀ z hz).trans he
    have he₀ : V.subtype (P.reverse.eval₂ c z)=0 :=
      (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero _ hx₀)
    have hzr₀ : P.reverse.eval₂ c z=0 :=
      V.subtype_injective (he₀.trans (map_zero V.subtype).symm)
    exact reverse_residue_ne V c hP z hzr (by rw [hzr₀,map_zero])
  intro A B h
  apply sub_eq_zero.mp
  apply hZero
  have hab : e A=e B := h
  change e (A-B)=0
  rw [map_sub,hab,sub_self]

/-- The numerator degree bound below the denominator degree makes
the literal evaluated quotient integral at this same pole. -/
theorem degree_le_at_pole_integral {x : F} (hx : x ∉ V)
    (A B : k[X]) (hB : B≠0) (hdeg : A.natDegree ≤ B.natDegree) :
    A.eval₂ (V.subtype.comp c) x / B.eval₂ (V.subtype.comp c) x ∈ V := by
  have hx₀ : x≠0 := fun h => hx (h.symm ▸ V.zero_mem)
  obtain ⟨z,hz,hzr⟩ := inverse_small V hx
  let a := A.reverse.eval₂ c z
  let b := B.reverse.eval₂ c z
  have hbr : residue V b≠0 := reverse_residue_ne V c hB z hzr
  obtain ⟨q,hq,_⟩ := ratio_over_residue_unit V a b hbr
  have hQ : V.subtype a/V.subtype b ∈ V := by
    rw [←hq]
    exact q.property
  have hA : V.subtype a*x^A.natDegree=A.eval₂ (V.subtype.comp c) x :=
    reverse_eval V c A hx₀ z hz
  have hD : V.subtype b*x^B.natDegree=B.eval₂ (V.subtype.comp c) x :=
    reverse_eval V c B hx₀ z hz
  let d := B.natDegree-A.natDegree
  have he : x^B.natDegree=x^A.natDegree*x^d := by
    rw [←pow_add,show A.natDegree+d=B.natDegree from Nat.add_sub_of_le hdeg]
  have hd : x^A.natDegree/x^B.natDegree=(x⁻¹)^d := by
    rw [he,←div_div,div_self (pow_ne_zero _ hx₀),one_div,inv_pow]
  have hz' : x⁻¹ ∈ V := by
    rw [←hz]
    exact z.property
  rw [←hA,←hD,←div_mul_div_comm,hd]
  exact V.mul_mem hQ (V.pow_mem hz' _)

end ActualGaussianWeberValuedPolynomialPole318
