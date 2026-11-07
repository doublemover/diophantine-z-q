module
public import InertSelectedContact318
public import RawRootPoints318
public section
namespace FiniteScale318
open ConcreteG8Domain LocalGenerator318 CircuitReplay Raw318FinalReplay
open RawAnchorNorm318 RawWeights318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Both real embeddings of the actual quadratic field. -/
@[expose] noncomputable def realPlace (r:ℝ) (hr:r^2=2) : K →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨r,by simpa [pow_two,Algebra.smul_def] using hr⟩

theorem realPlace_pair (r:ℝ) (hr:r^2=2) (a b:ℚ) :
    realPlace r hr (pair a b)=(a:ℝ)+(b:ℝ)*r := by
  simp [realPlace,QuadraticAlgebra.lift_apply_apply,pair,Algebra.smul_def]

/-- The two conjugates of D are both strictly greater than one. -/
theorem D_real_gt_one (r:ℝ) (hr:r^2=2) : 1<realPlace r hr D := by
  have hd : D=pair 11 (-6) := by ext <;> norm_num [D,i,pair,pow_two]
  rw [hd]
  rw [realPlace_pair]
  norm_num
  nlinarith [sq_nonneg (r-5/3)]

/-- Every source square-root point is outside [-1,1] at both real places. -/
theorem root_abs_gt_one (r:ℝ) (hr:r^2=2) (h j:K) (hj:j^2=h^4-D) :
    1 < |realPlace r hr h| := by
  have he := congrArg (realPlace r hr) hj
  simp only [map_pow,map_sub] at he
  have hd := D_real_gt_one r hr
  by_contra! hh
  have hs: (realPlace r hr h)^2≤1 := by
    rw [←sq_abs]
    nlinarith [abs_nonneg (realPlace r hr h)]
  have h4:(realPlace r hr h)^4≤1 := by
    nlinarith [sq_nonneg (realPlace r hr h),sq_nonneg ((realPlace r hr h)^2-1)]
  nlinarith [sq_nonneg (realPlace r hr j)]

/-- The stored pair is exactly the product of the four literal roots. -/
theorem product_pair (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    pair (w 143) (w 144)=∏i,root w i := by
  have h100:r100 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=100)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r100] at h100
  have h101:r101 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=101)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r101] at h101
  have h102:r102 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=102)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r102] at h102
  have h103:r103 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=103)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r103] at h103
  have h104:r104 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=104)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r104] at h104
  have h105:r105 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=105)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r105] at h105
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
  rw [hp3,hp2,hp,Fin.prod_univ_four]
  ring

theorem product_real_abs_gt_one (r:ℝ) (hr:r^2=2) (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) :
    1 < |realPlace r hr (pair (w 143) (w 144))| := by
  have hb (i:Fin 4):1 < |realPlace r hr (root w i)| := by
    obtain ⟨j,hj,-⟩ := RawRootPoints318.all_root_factors S w source i
    exact root_abs_gt_one r hr _ _ hj
  rw [product_pair S w source,Fin.prod_univ_four]
  simp only [map_mul,abs_mul]
  have h01:1 < |realPlace r hr (root w 0)| * |realPlace r hr (root w 1)| := by nlinarith [hb 0,hb 1]
  have h012:1 < |realPlace r hr (root w 0)| * |realPlace r hr (root w 1)| * |realPlace r hr (root w 2)| := by nlinarith [hb 2]
  nlinarith [hb 3]

/-- If both conjugates have magnitude greater than one, the norm cannot
cancel the rational part. This is real algebra, independent of group labels. -/
theorem norm_add_re_ne_zero (a b:ℚ)
    (hp:1 < |(a:ℝ)+(b:ℝ)*Real.sqrt 2|)
    (hm:1 < |(a:ℝ)-(b:ℝ)*Real.sqrt 2|) :
    a^2-2*b^2+a≠0 := by
  let u:ℝ := (a:ℝ)+(b:ℝ)*Real.sqrt 2
  let v:ℝ := (a:ℝ)-(b:ℝ)*Real.sqrt 2
  have hu:1 < |u| := hp
  have hv:1 < |v| := hm
  have hsum:|u+v|≤|u|+|v| := abs_add_le u v
  have hprod:|u|+|v| < 2 * |u*v| := by
    rw [abs_mul]
    nlinarith
  intro heq
  have heqR:(a:ℝ)^2-2*(b:ℝ)^2+(a:ℝ)=0 := by exact_mod_cast heq
  have hs:(Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have he:2*(u*v)=-(u+v) := by
    dsimp [u,v]
    nlinarith
  have habs:2*|u*v|=|u+v| := by
    have hh := congrArg abs he
    simpa only [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<2),abs_neg] using hh
  linarith

theorem A0_ne_zero (S:ℚ) (w:Assignment) : A0 S w≠0 := by norm_num [A0]

theorem A2_ne_zero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) : A2 S w≠0 := by
  have hn:w 145≠0 := by
    rw [RawAnchorNorm318.product_norm S w source]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    obtain ⟨j,-,hh⟩ := RawRootPoints318.all_root_factors S w source i
    exact AnchorNorm318.norm_ne_zero hh
  simpa only [A2,div_self (by norm_num:(1:ℚ)≠0),one_mul] using mul_ne_zero hn hn

theorem A1_ne_zero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) : A1 S w≠0 := by
  have hn:w 145=(w 143)^2-2*(w 144)^2 := by
    have hh:r106 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=106)
      (by simp only [stage0,List.length_cons,List.length_nil]; decide))
    dsimp only [r106] at hh
    linear_combination hh
  have hp := product_real_abs_gt_one (Real.sqrt 2) (Real.sq_sqrt (by norm_num)) S w source
  have hm := product_real_abs_gt_one (-Real.sqrt 2) (by simpa only [neg_sq] using Real.sq_sqrt (by norm_num:(0:ℝ)≤2)) S w source
  rw [realPlace_pair] at hp hm
  have hne := norm_add_re_ne_zero (w 143) (w 144) hp (by simpa [sub_eq_add_neg] using hm)
  have hsum:w 143+w 145≠0 := by rw [hn]; convert hne using 1; ring
  have hscale:A1 S w=(w 143+w 145)^2 := by simp only [A1]; ring
  rw [hscale]
  exact pow_ne_zero _ hsum

end FiniteScale318
#print axioms FiniteScale318.root_abs_gt_one

#print axioms FiniteScale318.A1_ne_zero
#print axioms FiniteScale318.A2_ne_zero
