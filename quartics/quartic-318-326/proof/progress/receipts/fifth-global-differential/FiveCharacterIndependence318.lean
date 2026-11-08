module
public import ContactCharacterFiniteIndependence318
public import FifthFormLocalCoefficients318
public section
noncomputable section
namespace FiveCharacterIndependence318
open scoped BigOperators
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- Four complementary characters and the full-root character are separated
by the actual four root-sign automorphisms. No dimension assertion is used. -/
theorem coefficients_zero {F L:Type*} [Field F] [Field L] [CharZero L] [Algebra F L]
    (v:Fin 4→L) (hv:∀i,v i≠0) (w:L) (hw:w≠0) (σ:Fin 4→L≃ₐ[F]L)
    (hfix:∀i,σ i (v i)=v i) (hneg:∀i j,i≠j→σ i (v j)= -v j)
    (hwneg:∀i,σ i w= -w) (a:Fin 4→F) (c:F)
    (h:(∑j,algebraMap F L (a j)*v j)+algebraMap F L c*w=0) :
    (∀i,a i=0) ∧ c=0 := by
  have ha:∀i,a i=0:=by
    intro i
    let b:Fin 4→L:=fun j=>algebraMap F L (a j)*v j
    let d:L:=algebraMap F L c*w
    have hb (j:Fin 4):σ i (b j)=if j=i then b j else -b j := by
      dsimp only [b]
      rw [map_mul,AlgEquiv.commutes]
      by_cases he:j=i
      · subst j;rw [hfix,if_pos rfl]
      · rw [hneg i j (Ne.symm he),if_neg he,mul_neg]
    have hd:σ i d= -d:=by
      dsimp only [d]
      rw [map_mul,AlgEquiv.commutes,hwneg,mul_neg]
    have hs : b i+(∑j∈Finset.univ.erase i,b j)+d=0 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      exact h
    have ht : b i-(∑j∈Finset.univ.erase i,b j)-d=0 := by
      have he:=congrArg (σ i) h
      change σ i ((∑j,b j)+d)=σ i 0 at he
      rw [map_add,map_sum,map_zero,hd,←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at he
      rw [hb,if_pos rfl] at he
      have hn:∑j∈Finset.univ.erase i,σ i (b j)= -(∑j∈Finset.univ.erase i,b j) := by
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hb,if_neg (Finset.mem_erase.mp hj).1]
      rw [hn] at he
      simpa only [sub_eq_add_neg] using he
    have hbi:b i=0 := by
      have htwo:(2:L)*b i=0 := by linear_combination hs+ht
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hz:algebraMap F L (a i)=0 := (mul_eq_zero.mp hbi).resolve_right (hv i)
    exact (algebraMap F L).injective (hz.trans (map_zero _).symm)
  refine ⟨ha,?_⟩
  simp only [ha,map_zero,zero_mul,Finset.sum_const_zero,zero_add] at h
  exact (algebraMap F L).injective
    (((mul_eq_zero.mp h).resolve_right hw).trans (map_zero _).symm)
end FiveCharacterIndependence318
