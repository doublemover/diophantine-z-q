module
public import RawRootDifference318
public section
namespace AlternateFormal318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay RawDetector318 SourceContact318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- A positive delta fixes the positive reciprocal branch and its exact
quartic depth. The identity chart is handled separately, with no finite
valuation assigned to zero. -/
theorem positive_delta {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D u y : F) (hD : v D=0) (h2 : v (2:F)=0)
    (hc : y^2=1-D*u^4) (hp : 0<v (y-1)) :
    (u=0 ∧ y=1) ∨ ∃a:ℤ,1≤a ∧ v u=(a:ℤ) ∧ v (y-1)=(4*a:ℤ) ∧ v y=0 := by
  have hplus : v (y+1)=0 := by
    have he : y+1=(y-1)+2 := by ring
    rw [he,v.map_add_eq_of_lt_right (by simpa [h2] using hp),h2]
  have hid : (y-1)*(y+1)=-(D*u^4) := by linear_combination hc
  by_cases hz : y-1=0
  · left
    have hy : y=1 := sub_eq_zero.mp hz
    have hD0 : D≠0 := (v.ne_top_iff).mp (by rw [hD]; simp)
    have hu4 : u^4=0 := by
      rw [hz,zero_mul] at hid
      exact (mul_eq_zero.mp (neg_eq_zero.mp hid.symm)).resolve_left hD0
    exact ⟨(pow_eq_zero_iff (by decide : 4≠0)).mp hu4,hy⟩
  · right
    have hu0 : u≠0 := by
      intro hu
      rw [hu,zero_pow (by decide : 4≠0),mul_zero,neg_zero] at hid
      have hpz := (mul_eq_zero.mp hid).resolve_left hz
      rw [hpz,v.map_zero] at hplus
      exact WithTop.top_ne_coe hplus
    obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hu0)
    obtain ⟨c,hcv⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hz)
    have hcpos : 0<c := by rw [←hcv] at hp; exact_mod_cast hp
    have hca := ValuationCurveParity.positive_case v D u y hD h2 hc a c ha.symm hcv.symm hcpos
    have hapos : 0<a := by omega
    refine ⟨a,by omega,ha.symm,?_,?_⟩
    · simpa [hca] using hcv.symm
    · exact ValuationLucasOrientation318.ordinate_unit v D u y hD
        (by rw [←ha]; exact_mod_cast hapos) hc

@[expose] def u (w:Assignment) (j:Fin 4) : K := conj (RawRootDifference318.u w j)
@[expose] def y (w:Assignment) (j:Fin 4) : K := conj (RawRootDifference318.v w j)
@[expose] def leaf (S:ℚ) (w:Assignment) : Fin 4 → K := ![leaf6 S w,leaf7 S w,leaf8 S w,leaf9 S w]

theorem source_curves (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w) :
    ∀j,(y w j)^2=1-pair 11 6*(u w j)^4 := by
  intro j
  have hh := congrArg conj (RawRootDifference318.source_curves S w source j)
  have hDc : conj CompressedOrientation318.D=pair 11 6 := by
    ext <;> norm_num [conj,CompressedOrientation318.D,pair]
  simpa only [map_pow,map_sub,map_one,map_mul,hDc,u,y] using hh

theorem source_leaves (S:ℚ) (w:Assignment) : ∀j,leaf S w j=y w j-1 := by
  intro j
  fin_cases j <;> ext <;>
    norm_num [leaf,y,RawRootDifference318.v,RawAlternatePade318.v1,RawAlternatePade318.v2,
      RawAlternatePade318.v3,RawAlternatePade318.v4,leaf6,leaf7,leaf8,leaf9,conj,pair] <;> ring

/-- The actual four linear leaves, not squared replacements, give exactly
the branch and depths required by the J-series precision theorem. -/
theorem source_positive_branches (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (v:AddValuation K (WithTop ℤ)) (hD:v (pair 11 6)=0) (h2:v (2:K)=0)
    (hb:∀j,(2:WithTop ℤ)≤v (leaf S w j)) :
    ∀j,(u w j=0 ∧ y w j=1) ∨
      ∃a:ℤ,1≤a ∧ v (u w j)=(a:ℤ) ∧ v (y w j-1)=(4*a:ℤ) ∧ v (y w j)=0 := by
  intro j
  apply positive_delta v _ _ _ hD h2 (source_curves S w source j)
  have hp := hb j
  rw [source_leaves S w j] at hp
  exact lt_of_lt_of_le (by norm_num) hp

end AlternateFormal318
