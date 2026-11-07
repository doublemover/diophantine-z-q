module
public import RawAnchor318
public import AnchorNorm318
public section
namespace RawAnchorNorm318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain AnchorNorm318
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] def root (w : Assignment) : Fin 4 → K :=
  ![pair (w 79) (w 80),pair (w 82) (w 83),pair (w 85) (w 86),pair (w 88) (w 89)]

@[expose] def scalarRoot (w : Assignment) : K := pair (w 303) (w 304)

theorem product_norm (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    w 145=∏i,norm (root w i) := by
  have h100 : r100 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=100)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r100] at h100
  have h101 : r101 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=101)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r101] at h101
  have h102 : r102 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=102)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r102] at h102
  have h103 : r103 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=103)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r103] at h103
  have h104 : r104 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=104)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r104] at h104
  have h105 : r105 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=105)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r105] at h105
  have h106 : r106 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=106)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r106] at h106
  have hp : pair (w 139) (w 140)=root w 0*root w 1 := by
    change pair (w 139) (w 140)=pair (w 79) (w 80)*pair (w 82) (w 83)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h100; linear_combination h101]
  have hp2 : pair (w 141) (w 142)=root w 2*pair (w 139) (w 140) := by
    change pair (w 141) (w 142)=pair (w 85) (w 86)*pair (w 139) (w 140)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h102; linear_combination h103]
  have hp3 : pair (w 143) (w 144)=root w 3*pair (w 141) (w 142) := by
    change pair (w 143) (w 144)=pair (w 88) (w 89)*pair (w 141) (w 142)
    rw [pair_product]
    ext <;> simp only [pair] <;> [linear_combination h104; linear_combination h105]
  have hn : w 145=norm (pair (w 143) (w 144)) := by
    rw [norm_pair]
    linear_combination h106
  rw [hn,hp3,hp2,hp,AnchorNorm318.norm_mul,AnchorNorm318.norm_mul,AnchorNorm318.norm_mul,Fin.prod_univ_four]
  ring

theorem scalar_inverse_norm (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    w 308=(norm (scalarRoot w))⁻¹ ∧ norm (scalarRoot w)≠0 ∧ w 308≠0 := by
  have h274 : r274 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=274)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r274] at h274
  have h275 : r275 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=275)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r275] at h275
  have hnorm : norm (scalarRoot w)=w 307 := by
    rw [scalarRoot,norm_pair]
    linear_combination -h274
  have hmul : norm (scalarRoot w)*w 308=1 := by
    rw [hnorm]
    linear_combination h275
  have hn : norm (scalarRoot w)≠0 := left_ne_zero_of_mul_eq_one hmul
  refine ⟨?_,hn,right_ne_zero_of_mul_eq_one hmul⟩
  rw [inv_eq_one_div]
  exact (eq_div_iff hn).mpr (by simpa [mul_comm] using hmul)

/-- The exact root-product valuation is derived from four actual square
abscissae and their elliptic norm values, not assumed as a product premise. -/
theorem product_two_value (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (labels : Fin 4 → ℤ) (x : Fin 4 → K) (hx : ∀i,(root w i)^2=x i)
    (hval : ∀i,padicValRat 2 (norm (x i))= -6-4*(padicValInt 2 (labels i):ℤ)) :
    padicValRat 2 (4096*w 145)= -2*(∑i,(padicValInt 2 (labels i):ℤ)) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hv (i : Fin 4) : padicValRat 2 (norm (root w i))= -3-2*(padicValInt 2 (labels i):ℤ) :=
    root_norm_value 2 _ _ (hx i) _ (by rw [hval]; ring)
  have hn (i : Fin 4) : norm (root w i)≠0 := by
    intro hz
    have hh := hv i
    rw [hz,padicValRat.zero] at hh
    omega
  have hc : padicValRat 2 (4096:ℚ)=12 := by
    change padicValRat 2 ((2:ℚ)^12)=12
    have h2 : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
    rw [padicValRat.pow,h2]
    norm_num
  rw [product_norm S w source,Fin.prod_univ_four]
  rw [padicValRat.mul (by norm_num) (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3)),hc]
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)) (hn 3),
    padicValRat.mul (mul_ne_zero (hn 0) (hn 1)) (hn 2),padicValRat.mul (hn 0) (hn 1)]
  simp only [hv,Fin.sum_univ_four]
  ring

/-- At 3, four unit square abscissae force the raw root-product term to be a
unit, as required by the affine anchor after oddness has been proved. -/
theorem product_three_value (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (x : Fin 4 → K) (hx : ∀i,(root w i)^2=x i)
    (hval : ∀i,padicValRat 3 (norm (x i))=0) (hn : ∀i,root w i≠0) :
    padicValRat 3 (4096*w 145)=0 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hv (i : Fin 4) : padicValRat 3 (norm (root w i))=0 :=
    root_norm_value 3 _ _ (hx i) 0 (by simpa using hval i)
  have hn' (i : Fin 4) := norm_ne_zero (hn i)
  have hc : padicValRat 3 (4096:ℚ)=0 := by
    simpa using rational_unit_value 3 4096 1 (by norm_num) (by norm_num)
  rw [product_norm S w source,Fin.prod_univ_four]
  rw [padicValRat.mul (by norm_num) (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn' 0) (hn' 1)) (hn' 2)) (hn' 3)),hc]
  rw [padicValRat.mul (mul_ne_zero (mul_ne_zero (hn' 0) (hn' 1)) (hn' 2)) (hn' 3),
    padicValRat.mul (mul_ne_zero (hn' 0) (hn' 1)) (hn' 2),padicValRat.mul (hn' 0) (hn' 1)]
  simp only [hv,add_zero]

theorem scalar_two_value (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (c : ℤ) (x : K) (hx : (scalarRoot w)^2=x)
    (hval : padicValRat 2 (norm x)= -6-4*(padicValInt 2 c:ℤ)) :
    padicValRat 2 (w 308)=3+2*(padicValInt 2 c:ℤ) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [(scalar_inverse_norm S w source).1]
  exact inverse_root_norm_value 2 _ _ hx _ (by rw [hval]; ring)

theorem scalar_three_value (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (c : ℤ) (x : K) (hx : (scalarRoot w)^2=x)
    (hval : padicValRat 3 (norm x)= -4-4*(padicValInt 3 c:ℤ)) :
    padicValRat 3 (w 308)=2+2*(padicValInt 3 c:ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [(scalar_inverse_norm S w source).1]
  exact inverse_root_norm_value 3 _ _ hx _ (by rw [hval]; ring)

/-- Source-specific anchor conclusion after individual elliptic valuation
facts have been supplied. The raw product, inverse, semilocal conic, parity,
and scalar-index arithmetic are all proved, not bundled into hypotheses. -/
theorem source_anchor_from_individual_point_data (w : Assignment)
    (source : Constraints (stage0 ((3:ℚ)^65536)) w) (labels : Fin 4 → ℤ)
    (hn : ∀i,labels i≠0) (c : ℤ) (hc : c≠0)
    (horient : c=labels 1-1 ∨ c= -labels 1-1)
    (hroot2 : ∀i,padicValRat 2 (norm ((root w i)^2))=
      -6-4*(padicValInt 2 (labels i):ℤ))
    (hscalar2 : padicValRat 2 (norm ((scalarRoot w)^2))=
      -6-4*(padicValInt 2 c:ℤ))
    (hroot3 : ∀i,Odd (labels i) → padicValRat 3 (norm ((root w i)^2))=0)
    (hscalar3 : Even c → padicValRat 3 (norm ((scalarRoot w)^2))=
      -4-4*(padicValInt 3 c:ℤ)) :
    (∀i,Odd (labels i)) ∧ (2*3^32767:ℤ)∣c ∧ (2:ℝ)^49151<(c.natAbs:ℝ) := by
  have hR := scalar_inverse_norm _ w source
  have hbase := scalar_two_value _ w source c _ rfl hscalar2
  have hprod := product_two_value _ w source labels _ (fun _ => rfl) hroot2
  have hodd := RawAnchor318.source_odd_labels_from_norm_values w source labels hn c hR.2.2 hbase hprod
  have heven : Even c := by
    obtain ⟨j,hj⟩ := hodd 1
    rcases horient with h | h
    · exact ⟨j,by omega⟩
    · exact ⟨-j-1,by omega⟩
  have hnroot (i : Fin 4) : root w i≠0 := by
    intro h
    have hh := hroot2 i
    rw [h,zero_pow (by decide : 2≠0)] at hh
    simp only [AnchorNorm318.norm,QuadraticAlgebra.norm_zero,padicValRat.zero] at hh
    omega
  have hprod3 := product_three_value _ w source _ (fun _ => rfl)
    (fun i => hroot3 i (hodd i)) hnroot
  refine ⟨hodd,RawAnchor318.source_scalar_index_bound w source c hc heven hR.2.2 ?_ ?_⟩
  · exact scalar_three_value _ w source c _ rfl (hscalar3 heven)
  · omega

end RawAnchorNorm318
