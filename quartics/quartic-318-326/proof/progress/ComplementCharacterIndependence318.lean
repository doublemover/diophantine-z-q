module
public import SourceCharacterFields318
public section
noncomputable section
namespace ComplementCharacterIndependence318
open scoped BigOperators
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Distinct sign characters are separated using their actual automorphisms.
The coefficient field and the original ambient field are kept explicit. -/
theorem coefficients_zero {F L:Type*} [Field F] [Field L] [CharZero L] [Algebra F L]
    (v:Fin 4→L) (hv:∀i,v i≠0) (σ:Fin 4→L≃ₐ[F]L)
    (hfix:∀i,σ i (v i)=v i) (hneg:∀i j,i≠j→σ i (v j)= -v j)
    (a:Fin 4→F) (h:∑j,algebraMap F L (a j)*v j=0) : ∀i,a i=0 := by
  intro i
  let b:Fin 4→L:=fun j=>algebraMap F L (a j)*v j
  have hb (j:Fin 4):σ i (b j)=if j=i then b j else -b j := by
    dsimp only [b]
    rw [map_mul,AlgEquiv.commutes]
    by_cases he:j=i
    · subst j
      rw [hfix,if_pos rfl]
    · rw [hneg i j (Ne.symm he),if_neg he,mul_neg]
  have hs : b i+∑j∈Finset.univ.erase i,b j=0 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    exact h
  have ht : b i-∑j∈Finset.univ.erase i,b j=0 := by
    have he:=congrArg (σ i) h
    change σ i (∑j,b j)=σ i 0 at he
    rw [map_sum,map_zero,←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at he
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
  have ha:algebraMap F L (a i)=0 := (mul_eq_zero.mp hbi).resolve_right (hv i)
  exact (algebraMap F L).injective (ha.trans (map_zero _).symm)

variable (c:Fin 4→ℚˣ)
abbrev L:=KummerTensorField318.Raw (SourceKummerField318.parameter c)
local instance field : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance charZero : CharZero (L c):=Algebra.charZero_of_charZero (RatFunc ℚ) (L c)
@[expose] def root (i:Fin 4):L c:=
  CharacterRoot318.root (SourceKummerField318.parameter c) (SourceCharacterFields318.complement i)
@[expose] def flip (i:Fin 4):L c≃ₐ[RatFunc ℚ]L c:=
  FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (SourceCharacterFields318.flip i)

theorem flip_self (i:Fin 4):flip c i (root c i)=root c i := by
  apply (CharacterRoot318.sign_fixes_iff _ _ _).mpr
  apply Finset.prod_eq_one
  intro j hj
  have hn:j≠i:=(Finset.mem_erase.mp hj).1
  simp [CharacterRoot318.sign,SourceCharacterFields318.flip,hn]

theorem inverse_roots_independent (a:Fin 4→RatFunc ℚ)
    (h:∑j,algebraMap (RatFunc ℚ) (L c) (a j)*(root c j)⁻¹=0) : ∀j,a j=0 := by
  apply coefficients_zero (fun j=>(root c j)⁻¹)
    (fun j=>inv_ne_zero (CharacterRoot318.root_ne_zero _ _)) (flip c)
    (fun i=>by rw [map_inv₀,flip_self])
    (fun i j hij=>by
      rw [map_inv₀]
      change (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
        (SourceCharacterFields318.flip i)
          (CharacterRoot318.root (SourceKummerField318.parameter c) (SourceCharacterFields318.complement j)))⁻¹=_
      rw [SourceCharacterFields318.other_flip_negates c j i hij,inv_neg]
      rfl) a h
end ComplementCharacterIndependence318
