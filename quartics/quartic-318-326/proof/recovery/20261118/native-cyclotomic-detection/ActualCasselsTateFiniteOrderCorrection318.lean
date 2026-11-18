module
public import ActualCasselsTateFiniteThreeProduct318
public import ActualCasselsTateCofinalFiniteInflation318
import all ActualCasselsTateFiniteDomainCocycles318
import all ActualCasselsTateFiniteDomainFactor318
import all ActualCasselsTateFiniteCoefficientField318
import all ActualCasselsTateContinuousThirdObstruction318
public section
noncomputable section
namespace ActualCasselsTateFiniteOrderCorrection318
open ActualCasselsTateFiniteThreeProduct318 ActualCasselsTateCofinalFiniteInflation318
open ActualCasselsTateFiniteDomainCocycles318 ActualCasselsTateFiniteDomainFactor318
open ActualCasselsTateFiniteCoefficientField318 ActualCasselsTateContinuousThirdObstruction318
open ActualCasselsTateUnitCoefficients318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "U" => (AlgebraicClosure F)ˣ
local notation "G" => Field.absoluteGaloisGroup F

/-- All positive powers admit pointwise roots in the algebraic closure;
no chosen root is presumed fixed by the old finite Galois kernel. -/
private lemma exists_unit_root (u : U) (m : ℕ) (hm : 0 < m) : ∃ v : U, v^m=u := by
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (u : AlgebraicClosure F) hm
  have hv0 : v ≠ 0 := by
    intro h
    exact u.ne_zero (by simpa only [h,zero_pow (Nat.ne_of_gt hm)] using hv.symm)
  exact ⟨Units.mk0 v hv0,Units.ext hv⟩

/-- Correct an arbitrary locally constant degree-three cocycle by an
actual global two-cochain so that its residual values all lie in one finite
roots-of-unity group. No real detection or global reciprocity is used. -/
theorem finite_order_correction (K : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (z : continuousUnitThreeCocycles (F:=F)) :
    ∃ (m : ℕ) (_ : 0 < m) (b : continuousUnitTwo (F:=F)),
      (z / continuousUnitDTwo b)^m = 1 := by
  classical
  obtain ⟨L,C,_,hf,_,_,_,hval,hC⟩ := exists_finite_three_cocycle_above K z
  letI : Finite (L ≃ₐ[F] L) := hf
  letI : Fintype (L ≃ₐ[F] L) := Fintype.ofFinite _
  let m := Fintype.card (L ≃ₐ[F] L)
  have hm : 0 < m := Fintype.card_pos
  let A : (L ≃ₐ[F] L) → (L ≃ₐ[F] L) → Lˣ := fun x y => (productLast C x y)⁻¹
  let s := inflateFiniteTwo L A
  have hs : continuousUnitDTwo s = z^m := by
    apply Subtype.ext
    funext p
    rcases p with ⟨g,h,l⟩
    change unitDTwo _ g h l = (z (g,h,l))^m
    rw [←hval g h l,←map_pow]
    calc
      _ = coefficientUnitInclusion L (finiteGroupDTwo L A
        (finiteRestriction L g) (finiteRestriction L h) (finiteRestriction L l)) :=
          (finiteGroupDTwo_inflation L A g h l).symm
      _ = _ := congrArg (coefficientUnitInclusion L)
        (inverse_product_primitive (quotientUnitAction L) C hC _ _ _)
  let root (u : U) : U := Classical.choose (exists_unit_root u m hm)
  let b : continuousUnitTwo (F:=F) := ⟨fun t => root (s t),s.property.comp root⟩
  have hb : b^m = s := by
    apply Subtype.ext
    funext t
    exact Classical.choose_spec (exists_unit_root (s t) m hm)
  refine ⟨m,hm,b,?_⟩
  rw [div_pow,←map_pow,hb,hs,div_self]
end ActualCasselsTateFiniteOrderCorrection318
