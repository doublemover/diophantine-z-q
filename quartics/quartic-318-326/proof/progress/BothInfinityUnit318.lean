module
public import BothInfinityAlgebra318
public section
namespace BothInfinityUnit318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R T:Type*} [CommRing R] [CommRing T]

/-- On every coefficient algebra, a zero first input gives the unchanged second input. -/
theorem left_identity (A B:R) (φ:OutputRing A B →+* T)
    (hu:φ (u1 A B)=0) (hv:φ (v1 A B)=0) :
    φ (outU A B)=φ (u2 A B) ∧ φ (outV A B)=φ (v2 A B) := by
  have hb : φ (intercept A B)=0 := by simp only [intercept,map_sub,map_mul,hu,hv,mul_zero,sub_zero]
  have hd : φ (d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
      (slope A B) (intercept A B))=0 := by simp only [d,map_add,map_mul,hb,mul_zero,add_zero]
  have hout : φ (outU A B)=φ (u2 A B) := by
    simp only [outU,map_add,map_mul,hd,hu,zero_mul,zero_add,add_zero]
  refine ⟨hout,?_⟩
  have hh := congrArg φ (line_second A B)
  simp only [map_add,map_mul,hb,add_zero] at hh
  simp only [outV,map_sub,map_mul,hout,hb,sub_zero]
  exact hh.symm

/-- The second-input identity law includes nilpotent coefficient directions. -/
theorem right_identity (A B:R) (φ:OutputRing A B →+* T)
    (hu:φ (u2 A B)=0) (hv:φ (v2 A B)=0) :
    φ (outU A B)=φ (u1 A B) ∧ φ (outV A B)=φ (v1 A B) := by
  have hb : φ (intercept A B)=0 := by
    have hh := congrArg φ (line_second A B)
    simpa only [map_add,map_mul,hu,hv,mul_zero,zero_add] using hh.symm
  have hd : φ (d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
      (slope A B) (intercept A B))=0 := by simp only [d,map_add,map_mul,hb,mul_zero,add_zero]
  have hout : φ (outU A B)=φ (u1 A B) := by
    simp only [outU,map_add,map_mul,hd,hu,zero_mul,zero_add,add_zero]
  refine ⟨hout,?_⟩
  have hh := congrArg φ (line_first A B)
  simp only [map_add,map_mul,hb,add_zero] at hh
  simp only [outV,map_sub,map_mul,hout,hb,sub_zero]
  exact hh.symm

end BothInfinityUnit318
