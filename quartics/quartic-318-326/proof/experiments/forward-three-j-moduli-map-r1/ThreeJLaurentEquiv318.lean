module
public import ThreeJMonicAlgebra318
public section
noncomputable section
namespace ThreeJLaurentEquiv318
open Polynomial ThreeJMonicAlgebra318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Laurent := ProjectiveLineOverlap318.A

@[expose] def jLaurent : Laurent :=
  (ProjectiveLineOverlap318.t+27)*(ProjectiveLineOverlap318.t+243)^3*
    ProjectiveLineOverlap318.s^3
@[expose] def baseMap : Base →ₐ[ℚ] Laurent := Polynomial.aeval jLaurent

lemma laurent_relation : polynomial.eval₂ baseMap.toRingHom ProjectiveLineOverlap318.t=0 := by
  simp only [polynomial,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,
    map_sub,map_ofNat,baseMap,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X]
  have hpow : ProjectiveLineOverlap318.t^3*ProjectiveLineOverlap318.s^3=1 := by
    rw [←mul_pow,ProjectiveLineOverlap318.ts,one_pow]
  unfold jLaurent
  linear_combination -((ProjectiveLineOverlap318.t+27)*
    (ProjectiveLineOverlap318.t+243)^3)*hpow

/-- Send the universal quartic root to the exact original Laurent parameter,
and its coefficient j to the exact global-map coordinate. -/
@[expose] def forward : Model →ₐ[ℚ] Laurent :=
  AdjoinRoot.liftAlgHom polynomial baseMap ProjectiveLineOverlap318.t laurent_relation

lemma forward_t : forward t=ProjectiveLineOverlap318.t := AdjoinRoot.liftAlgHom_root ..
lemma forward_base (p : Base) : forward (algebraMap Base Model p)=baseMap p :=
  AdjoinRoot.liftAlgHom_of ..
lemma forward_j : forward j=jLaurent := by rw [j,forward_base]; exact Polynomial.aeval_X _

/-- The inverse uses the genuine localization universal property; the
quartic relation supplies invertibility of the actual root. -/
@[expose] def backward : Laurent →ₐ[ℚ] Model :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) t) (X:ℚ[X])
    (by simpa only [Polynomial.aeval_X] using t_unit)

lemma backward_base (p : ℚ[X]) :
    backward (algebraMap ℚ[X] Laurent p)=Polynomial.aeval (R:=ℚ) t p := by
  simp only [backward,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]

lemma backward_t : backward ProjectiveLineOverlap318.t=t := by
  rw [ProjectiveLineOverlap318.t,backward_base,Polynomial.aeval_X]

lemma backward_s : backward ProjectiveLineOverlap318.s=inverseT := by
  have h := congrArg backward ProjectiveLineOverlap318.ts
  simp only [map_mul,map_one,backward_t] at h
  calc
    _ = (t*inverseT)*backward ProjectiveLineOverlap318.s := by rw [t_inverseT,one_mul]
    _ = inverseT*(t*backward ProjectiveLineOverlap318.s) := by ring
    _ = inverseT := by rw [h,mul_one]

lemma backward_jLaurent : backward jLaurent=j := by
  simp only [jLaurent,map_mul,map_add,map_pow,map_ofNat,backward_t,backward_s]
  exact j_expression

/-- Actual rational-algebra equivalence with the original Laurent source
chart, not merely an abstract finite algebra with the same polynomial. -/
@[expose] def coordinateEquiv : Model ≃ₐ[ℚ] Laurent :=
  AlgEquiv.ofAlgHom forward backward
    (by
      apply IsLocalization.algHom_ext (Submonoid.powers (X:ℚ[X]))
      apply Polynomial.algHom_ext
      change forward (backward ProjectiveLineOverlap318.t)=ProjectiveLineOverlap318.t
      rw [backward_t,forward_t])
    (by
      apply AdjoinRoot.algHom_ext'
      · apply Polynomial.algHom_ext
        change backward (forward (algebraMap Base Model X))=algebraMap Base Model X
        rw [forward_base]
        change backward jLaurent=j
        exact backward_jLaurent
      · change backward (forward t)=t
        rw [forward_t,backward_t])

lemma coordinate_base (p : Base) : coordinateEquiv (algebraMap Base Model p)=baseMap p :=
  forward_base p
lemma coordinate_t : coordinateEquiv t=ProjectiveLineOverlap318.t := forward_t

/-- The universal quartic algebra is a domain because it is the actual
Laurent polynomial algebra, not by an assumed irreducibility assertion. -/
local instance laurent_domain : IsDomain Laurent :=
  Localization.Away.isDomain (Polynomial.X_ne_zero : (X:ℚ[X]) ≠ 0)

instance model_domain : IsDomain Model :=
  Function.Injective.isDomain coordinateEquiv.toRingHom coordinateEquiv.injective

end ThreeJLaurentEquiv318
