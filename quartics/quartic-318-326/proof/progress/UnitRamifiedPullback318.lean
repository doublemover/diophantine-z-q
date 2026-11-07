module
public import UnitFrameHorizontal318
public section
noncomputable section
namespace UnitRamifiedPullback318
open VerticalSection318 AlgebraicSectionPullback318
set_option maxHeartbeats 0

@[expose] def branchShift {S : Type*} [CommRing S] (i : Fin 4) (w : S) : S :=
  ∏ j : {j : Fin 4 // j ≠ i}, ((contacts i : S) - (contacts j : S) + w)
@[expose] def infinityShift {S : Type*} [CommRing S] (w : S) : S :=
  ∏ j : Fin 4, (1 - (contacts j : S)*w)

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
@[expose] def tangentFactor (D : Derivation R K K) (u z : K) : K := z*D u+2*u*D z

theorem finite_polynomial (i : Fin 4) (w : K) :
    denominator ((contacts i : K)+w) = w*branchShift i w := by
  classical
  unfold denominator branchShift
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [add_sub_cancel_left]
  rw [mul_comm]
  congr 1
  simp_rw [show ∀ j : Fin 4, (contacts i : K)+w-contacts j =
    (contacts i : K)-contacts j+w by intro j; ring]
  exact Finset.prod_subtype (Finset.univ.erase i) (by simp) _

theorem infinity_polynomial (w : K) (hw : w ≠ 0) :
    denominator (1/w) = infinityShift w / w^4 := by
  unfold denominator infinityShift
  have he (j : Fin 4) : (1:K)/w-contacts j = (1-(contacts j:K)*w)/w := by field_simp
  simp_rw [he]
  rw [Finset.prod_div_distrib]
  simp

theorem ramified_derivative (D : Derivation R K K) (u z : K) :
    D (u*z^2) = z*tangentFactor D u z := by
  rw [D.leibniz,D.leibniz_pow]
  simp only [tangentFactor, smul_eq_mul, nsmul_eq_mul]
  norm_num
  ring

theorem reciprocal_derivative (D : Derivation R K K) (w : K) :
    D (1/w) = -D w / w^2 := by
  rw [one_div,D.leibniz_inv]
  simp only [smul_eq_mul,div_eq_mul_inv,inv_pow]
  ring

theorem finite_coefficients (D : Derivation R K K) (i : Fin 4) (u z : K)
    (hu : u ≠ 0) (hz : z ≠ 0) :
    coefficient0 D ((contacts i : K)+u*z^2) =
      (tangentFactor D u z)^2/(u*branchShift i (u*z^2)) ∧
    coefficient1 D ((contacts i : K)+u*z^2) =
      ((contacts i : K)+u*z^2)*((tangentFactor D u z)^2/(u*branchShift i (u*z^2))) := by
  have h0 : coefficient0 D ((contacts i : K)+u*z^2) =
      (tangentFactor D u z)^2/(u*branchShift i (u*z^2)) := by
    rw [coefficient0,D.map_add,D.map_intCast,zero_add,ramified_derivative,finite_polynomial]
    by_cases hd : branchShift i (u*z^2)=0
    · simp [hd]
    · field_simp
  exact ⟨h0,by rw [coefficient1,h0]⟩

theorem infinity_coefficients (D : Derivation R K K) (u z : K)
    (hu : u ≠ 0) (hz : z ≠ 0) :
    coefficient0 D (1/(u*z^2)) = z^2*(tangentFactor D u z)^2/infinityShift (u*z^2) ∧
    coefficient1 D (1/(u*z^2)) = (tangentFactor D u z)^2/(u*infinityShift (u*z^2)) := by
  have hw : u*z^2 ≠ 0 := mul_ne_zero hu (pow_ne_zero _ hz)
  have h0 : coefficient0 D (1/(u*z^2)) = z^2*(tangentFactor D u z)^2/infinityShift (u*z^2) := by
    rw [coefficient0,reciprocal_derivative,ramified_derivative,infinity_polynomial _ hw]
    by_cases hd : infinityShift (u*z^2)=0
    · simp [hd]
    · field_simp
  refine ⟨h0,?_⟩
  rw [coefficient1,h0]
  by_cases hd : infinityShift (u*z^2)=0
  · simp [hd]
  · field_simp

end UnitRamifiedPullback318
