module
public import SourcePadicDetectorRegion318
public section
noncomputable section
namespace ActualOrbitBranchDepth318
open ConcreteG8Domain (K D)
open CoherentMultipleCharts318 CoherentAdditionV318 ScalarIndexValuations318
open ReciprocalGroup318 ReciprocalDouble318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The actual oriented chart, not just its square or elliptic quotient,
follows the precise plus-branch duplication formula. -/
lemma chartV_double (n : ℤ) : chartV (2*n)=vDouble D (chartU n) := by
  rw [show 2*n=n+n by ring,chartV_add,sumV_double D _ _ (CoherentAdditionV318.chart_curve n)]

lemma vDouble_sub_one (u : K) (hq : 1+D*u^4≠0) :
    vDouble D u-1= -(8:K)*D*u^4/(1+D*u^4)^2 := by
  unfold vDouble
  field_simp [hq] <;> ring

/-- Exact positive branch depth for every discrete valuation with D a unit.
This distinguishes v near+1 from the other reciprocal identity chart. -/
lemma branch_depth (v : AddValuation K (WithTop ℤ)) (u : K) (r s : ℤ)
    (hr : 0<r) (hu : v u=(r:WithTop ℤ)) (hD : v D=0)
    (h2 : v (2:K)=(s:WithTop ℤ)) :
    v (vDouble D u-1)=((3*s+4*r:ℤ):WithTop ℤ) := by
  have hs : v (D*u^4)=((4*r:ℤ):WithTop ℤ) := by
    rw [v.map_mul,v.map_pow,hD,hu,zero_add]
    norm_cast <;> simp [nsmul_eq_mul] <;> ring
  have hqv : v (1+D*u^4)=0 := by
    apply NormChainCompleteness.near_one_value v
    simpa only [add_sub_cancel_left] using (show 0<v (D*u^4) by rw [hs]; exact_mod_cast (by omega : 0<4*r))
  have hq : 1+D*u^4≠0 := (v.ne_top_iff).mp (by rw [hqv]; simp)
  have h8 : v (8:K)=((3*s:ℤ):WithTop ℤ) := by
    rw [show (8:K)=2^3 by norm_num,v.map_pow,h2]
    norm_cast <;> simp [nsmul_eq_mul] <;> ring
  rw [vDouble_sub_one u hq]
  simp only [v.map_div,v.map_pow,v.map_mul,v.map_neg,h8,hD,hu,hqv]
  norm_cast <;> simp [nsmul_eq_mul] <;> ring

lemma int_two_two (m : ℤ) (hm : m≠0) : padicValInt 2 (2*m)=1+padicValInt 2 m := by
  change padicValNat 2 (2*m).natAbs=1+padicValNat 2 m.natAbs
  rw [Int.natAbs_mul]
  change padicValNat 2 (2*m.natAbs)=1+padicValNat 2 m.natAbs
  rw [padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hm),padicValNat_self]

lemma int_four_two (m : ℤ) (hm : m≠0) : padicValInt 2 (4*m)=2+padicValInt 2 m := by
  rw [show 4*m=2*(2*m) by ring,int_two_two (2*m) (mul_ne_zero (by norm_num) hm),int_two_two m hm]
  omega

lemma int_two_three (m : ℤ) (hm : m≠0) : padicValInt 3 (2*m)=padicValInt 3 m := by
  change padicValNat 3 (2*m).natAbs=padicValNat 3 m.natAbs
  rw [Int.natAbs_mul]
  change padicValNat 3 (2*m.natAbs)=padicValNat 3 m.natAbs
  rw [padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr hm),
    padicValNat_primes (by decide : 3≠2),zero_add]

lemma int_four_three (m : ℤ) (hm : m≠0) : padicValInt 3 (4*m)=padicValInt 3 m := by
  rw [show 4*m=2*(2*m) by ring,int_two_three (2*m) (mul_ne_zero (by norm_num) hm),int_two_three m hm]

lemma two_u_place (m : ℤ) (hm : m≠0) :
    RamifiedTwo318.place (chartU (4*m))=((7+2*(padicValInt 2 m:ℤ):ℤ):WithTop ℤ) := by
  have hn : 4*m≠0 := mul_ne_zero (by norm_num) hm
  have hu : chartU (4*m)≠0 := fun h => hn ((chartU_zero_iff _).mp h)
  rw [RamifiedTwo318.place_norm _ hu,←ScalarTranslatedIndex318.norm_coefficient,
    chart_norm_two _ hn,int_four_two m hm]
  norm_cast <;> push_cast <;> ring

lemma three_u_place (m : ℤ) (hm : m≠0) :
    InertThree318.place (chartU (4*m))=((2+2*(padicValInt 3 m:ℤ):ℤ):WithTop ℤ) := by
  have hn : 4*m≠0 := mul_ne_zero (by norm_num) hm
  have hu : chartU (4*m)≠0 := fun h => hn ((chartU_zero_iff _).mp h)
  rw [InertThree318.place_norm _ hu,←ScalarTranslatedIndex318.norm_coefficient,
    chart_norm_three _ hn ⟨2*m,by ring⟩,int_four_three m hm]

/-- Actual plus-branch depths at both small places; these are independent of
any chosen real sign or a hypothetical p-adic orbit topology. -/
theorem two_v_place (m : ℤ) (hm : m≠0) :
    RamifiedTwo318.place (chartV (4*m)-1)=((26+8*(padicValInt 2 m:ℤ):ℤ):WithTop ℤ) := by
  have hn : 2*m≠0 := mul_ne_zero (by norm_num) hm
  have hu0 : chartU (2*m)≠0 := fun h => hn ((chartU_zero_iff _).mp h)
  have hu : RamifiedTwo318.place (chartU (2*m))=((5+2*(padicValInt 2 m:ℤ):ℤ):WithTop ℤ) := by
    rw [RamifiedTwo318.place_norm _ hu0,←ScalarTranslatedIndex318.norm_coefficient,
      chart_norm_two _ hn,int_two_two m hm]
    norm_cast <;> push_cast <;> ring
  rw [show 4*m=2*(2*m) by ring,chartV_double]
  have he := branch_depth RamifiedTwo318.place (chartU (2*m)) _ 2
    (by positivity) hu RamifiedTwo318.place_D RamifiedTwo318.place_two
  convert he using 1 <;> norm_cast <;> ring

theorem three_v_place (m : ℤ) (hm : m≠0) :
    InertThree318.place (chartV (4*m)-1)=((8+8*(padicValInt 3 m:ℤ):ℤ):WithTop ℤ) := by
  have hn : 2*m≠0 := mul_ne_zero (by norm_num) hm
  have hu0 : chartU (2*m)≠0 := fun h => hn ((chartU_zero_iff _).mp h)
  have hu : InertThree318.place (chartU (2*m))=((2+2*(padicValInt 3 m:ℤ):ℤ):WithTop ℤ) := by
    rw [InertThree318.place_norm _ hu0,←ScalarTranslatedIndex318.norm_coefficient,
      chart_norm_three _ hn ⟨m,by ring⟩,int_two_three m hm]
  rw [show 4*m=2*(2*m) by ring,chartV_double]
  have he := branch_depth InertThree318.place (chartU (2*m)) _ 0
    (by positivity) hu InertThree318.place_D InertThree318.place_two
  convert he using 1 <;> norm_cast <;> ring

end ActualOrbitBranchDepth318
