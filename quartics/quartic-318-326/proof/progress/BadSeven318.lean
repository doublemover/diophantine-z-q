module
public import RegularCuspGroup318
public import ActualDuplicationPlaces318
public section
namespace BadSeven318
open ConcreteG8Domain LocalGenerator318 NumberField WeierstrassCurve.Affine
open scoped QuadraticAlgebra
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_nat_le_one (w:FinitePlace K) (n:ℕ) : w (n:K)≤1 :=
  (show IsNonarchimedean (w ·) from FinitePlace.add_le w).apply_natCast_le_one (map_zero_le w 1) (map_one w)

theorem delta_small (w:FinitePlace K) (hD:w D<1) : w (3-i)<1 := by
  have hh : w (3-i)^2<1 := by simpa only [D,map_pow] using hD
  nlinarith [apply_nonneg w (3-i)]

theorem seven_small (w:FinitePlace K) (hD:w D<1) : w (7:K)<1 := by
  have hi:w i≤1 := by
    have hh:=congrArg (fun x:K=>w x) i_square
    rw [map_pow] at hh
    have h2 : w (2:K)≤1 := finite_nat_le_one w 2
    nlinarith [apply_nonneg w i]
  have hc:w (3+i)≤1 := (FinitePlace.add_le w _ _).trans (max_le (finite_nat_le_one w 3) hi)
  have hid:(3-i)*(3+i)=(7:K) := by linear_combination -i_square
  rw [←hid,map_mul]
  exact (mul_le_of_le_one_right (apply_nonneg w _) hc).trans_lt (delta_small w hD)

theorem finite_two_unit (w:FinitePlace K) (hD:w D<1) : w (2:K)=1 := by
  apply le_antisymm (finite_nat_le_one w 2)
  by_contra hh
  have h2:w (2:K)<1 := lt_of_not_ge hh
  have hprod:w (3*2:K)<1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg w (2:K)) (finite_nat_le_one w 3)).trans_lt h2
  have hsum:w ((7:K)+ -(3*2))<1 := (FinitePlace.add_le w _ _).trans_lt
    (max_lt (seven_small w hD) (by simpa only [map_neg_eq_map] using hprod))
  norm_num at hsum

theorem finite_three_unit (w:FinitePlace K) (hD:w D<1) : w (3:K)=1 := by
  apply le_antisymm (finite_nat_le_one w 3)
  by_contra hh
  have h3:w (3:K)<1 := lt_of_not_ge hh
  have hprod:w (2*3:K)<1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg w (3:K)) (finite_nat_le_one w 2)).trans_lt h3
  have hsum:w ((7:K)+ -(2*3))<1 := (FinitePlace.add_le w _ _).trans_lt
    (max_lt (seven_small w hD) (by simpa only [map_neg_eq_map] using hprod))
  norm_num at hsum

theorem finite_generator_unit (w:FinitePlace K) (hD:w D<1) : w xP=1 := by
  have hid:xP=(-(27:K)+28*(3-i))/8 := by
    ext <;> norm_num [xP,i,pair,QuadraticAlgebra.norm_def]
  have h8:w (8:K)=1 := by
    rw [show (8:K)=2^3 by norm_num,map_pow,finite_two_unit w hD]
    norm_num
  have h27:w (-(27:K))=1 := by
    rw [map_neg_eq_map,show (27:K)=3^3 by norm_num,map_pow,finite_three_unit w hD]
    norm_num
  have hsmall:w (28*(3-i))<w (-(27:K)) := by
    rw [h27,map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg w _) (finite_nat_le_one w 28)).trans_lt (delta_small w hD)
  rw [hid,map_div₀,(show IsNonarchimedean (w ·) from FinitePlace.add_le w).add_eq_left_of_lt (map_neg_eq_map w) hsmall,h27,h8]
  norm_num

/-- Every actual normalized finite place where D is nonunit has the same
weak finite sign for all integer multiples of the literal generator. -/
theorem all_multiples (w:FinitePlace K) (hD:w D<1) (n:ℤ) :
    1≤w ((n • P).xRep 0) := by
  exact RegularCuspGroup318.multiple_regular w.val (FinitePlace.add_le w) D hD
    (finite_nat_le_one w 2) P (by change 1≤w xP; rw [finite_generator_unit w hD]) n

end
end BadSeven318
#print axioms BadSeven318.all_multiples
