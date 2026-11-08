module
public import GammaHCuspEnds318
public import AllCuspQJ318
public section
noncomputable section
open Function UpperHalfPlane
open GammaHGroup318 GammaHDiamond318 GammaHAction318 GammaHCuspEnds318
open FiniteCuspEnds318 RotatedProjection318 FiniteCuspCoverage318
open scoped MatrixGroups
namespace GammaHCuspWidths318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Normalizing Gamma1 preserves its actual integral translation stabilizers. -/
theorem periods_matrix (N:ℕ) (H:Subgroup (ZMod N)ˣ) (g:gammaH N H) (r:SL(2,ℤ)) :
    RotatedWidths318.periods N (g.val*r)=RotatedWidths318.periods N r := by
  ext n
  change (g.val*r)*ModularGroup.T^n*(g.val*r)⁻¹∈CongruenceSubgroup.Gamma1 N ↔
    r*ModularGroup.T^n*r⁻¹∈CongruenceSubgroup.Gamma1 N
  constructor
  · intro hn
    have hh:=conjugate_gamma1 N H g⁻¹ _ hn
    simpa only [Subgroup.coe_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,
      mul_inv_cancel,inv_mul_cancel,mul_one] using hh
  · intro hn
    have hh:=conjugate_gamma1 N H g _ hn
    simpa only [mul_inv_rev,mul_assoc] using hh

/-- An integral upper triangular determinant-one matrix centralizes every
integer translation, including the negative-unipotent branch. -/
theorem upper_triangular_commute (k:SL(2,ℤ)) (hc:k 1 0=0) (n:ℤ) :
    k*ModularGroup.T^n=ModularGroup.T^n*k := by
  have hab:k 0 0*k 1 1=1 := by
    have h:=k.det_coe
    rwa [Matrix.det_fin_two,hc,mul_zero,sub_zero] at h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hab with ⟨ha,hd⟩|⟨ha,hd⟩
  all_goals ext i j;fin_cases i <;>fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
      ModularGroup.coe_T_zpow,hc,ha,hd,add_comm]

theorem gamma1_conjugate_iff (N:ℕ) (gamma:CongruenceSubgroup.Gamma1 N) (k:SL(2,ℤ)) :
    gamma.val*k*gamma.val⁻¹∈CongruenceSubgroup.Gamma1 N ↔ k∈CongruenceSubgroup.Gamma1 N := by
  constructor
  · intro hk
    have hh:=(CongruenceSubgroup.Gamma1 N).mul_mem
      ((CongruenceSubgroup.Gamma1 N).mul_mem ((CongruenceSubgroup.Gamma1 N).inv_mem gamma.property) hk)
      gamma.property
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one] using hh
  · intro hk
    exact (CongruenceSubgroup.Gamma1 N).mul_mem
      ((CongruenceSubgroup.Gamma1 N).mul_mem gamma.property hk)
      ((CongruenceSubgroup.Gamma1 N).inv_mem gamma.property)

/-- Equality of the actual high-neighborhood ends implies equality of the
actual translation stabilizers; no equality of cusp widths is assumed. -/
theorem periods_of_neighborhood_eq (N:ℕ) (r s:SL(2,ℤ))
    (hrs:neighborhood N r=neighborhood N s) :
    RotatedWidths318.periods N r=RotatedWidths318.periods N s := by
  have hi:¬Disjoint (cuspRegion N r 2) (cuspRegion N s 2) := by
    obtain ⟨z,hz⟩:=FiniteCuspEnds318.region_nonempty N r 2
    apply Set.not_disjoint_iff.mpr
    refine ⟨z,hz,?_⟩
    change z∈neighborhood N s
    change z∈neighborhood N r at hz
    rwa [←hrs]
  obtain ⟨gamma,hk⟩:=RotatedEndSeparation318.intersection_matrix N r s 2 2 (by norm_num) (by norm_num) hi
  let k:SL(2,ℤ):=s⁻¹*gamma.val*r
  have he:gamma.val*r=s*k := by dsimp [k];group
  ext n
  change r*ModularGroup.T^n*r⁻¹∈CongruenceSubgroup.Gamma1 N ↔
    s*ModularGroup.T^n*s⁻¹∈CongruenceSubgroup.Gamma1 N
  have hconj : gamma.val*(r*ModularGroup.T^n*r⁻¹)*gamma.val⁻¹=s*ModularGroup.T^n*s⁻¹ := by
    calc
      _ = (gamma.val*r)*ModularGroup.T^n*(gamma.val*r)⁻¹ := by group
      _ = (s*k)*ModularGroup.T^n*(s*k)⁻¹ := by rw [he]
      _ = s*(k*ModularGroup.T^n)*k⁻¹*s⁻¹ := by group
      _ = s*(ModularGroup.T^n*k)*k⁻¹*s⁻¹ := by rw [upper_triangular_commute k hk]
      _ = _ := by group
  rw [←hconj]
  exact (gamma1_conjugate_iff N gamma _).symm

theorem width_of_periods_eq (N:ℕ) (hN:0<N) (r s:SL(2,ℤ))
    (hrs:RotatedWidths318.periods N r=RotatedWidths318.periods N s) :
    RotatedWidths318.width N hN r=RotatedWidths318.width N hN s := by
  apply Nat.dvd_antisymm
  · have hs : (RotatedWidths318.width N hN s:ℤ)∈RotatedWidths318.periods N s :=
      (RotatedWidths318.period_iff N hN s _).mpr (dvd_refl _)
    rw [←hrs] at hs
    exact_mod_cast (RotatedWidths318.period_iff N hN r _).mp hs
  · have hr : (RotatedWidths318.width N hN r:ℤ)∈RotatedWidths318.periods N r :=
      (RotatedWidths318.period_iff N hN r _).mpr (dvd_refl _)
    rw [hrs] at hr
    exact_mod_cast (RotatedWidths318.period_iff N hN s _).mp hr

/-- Diamond transport preserves the already constructed fine-level cusp width.
This does not assert that quotient cusp widths are unchanged. -/
theorem matrixEnd_width (N:ℕ) (hN:5≤N) (H:Subgroup (ZMod N)ˣ)
    (g:gammaH N H) (c:End N) :
    AllCuspQJ318.natWidth N hN (matrixEnd N H g c)=AllCuspQJ318.natWidth N hN c := by
  apply width_of_periods_eq N (by omega)
  have he : neighborhood N (representative N (matrixEnd N H g c))=
      neighborhood N (g.val*representative N c) := representative_region N (matrixEnd N H g c)
  exact (periods_of_neighborhood_eq N _ _ he).trans (periods_matrix N H g (representative N c))

theorem diamondEnd_width (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    (u:H) (c:End N) :
    letI:=endDiamondAction N H
    AllCuspQJ318.natWidth N hN (u•c)=AllCuspQJ318.natWidth N hN c :=
  matrixEnd_width N hN H (lift N H u) c

end GammaHCuspWidths318
