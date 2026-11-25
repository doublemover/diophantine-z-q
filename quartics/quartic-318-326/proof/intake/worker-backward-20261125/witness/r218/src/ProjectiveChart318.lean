module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic
public section
noncomputable section
namespace ProjectiveChart318
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]
variable {σ : Type*}

/-- Actual homogeneous evaluation scales by the specified degree. -/
theorem eval_scaled {S : Type*} [CommRing S] [Fintype σ]
    (f : R →+* S) (p : MvPolynomial σ R) (n : ℕ) (hp : p.IsHomogeneous n)
    (t : S) (v : σ → S) : p.eval₂ f (fun i => t*v i)=t^n*p.eval₂ f v := by
  classical
  rw [eval₂_eq',eval₂_eq',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hn : ∑ i, d i=n := by
    rw [←Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  simp_rw [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,hn]
  ring

variable (R σ) [DecidableEq σ] (j : σ)
abbrev Grading := homogeneousSubmodule σ R
abbrev Chart := Away (Grading R σ) (X j)
abbrev FullLocalization := Localization.Away (X j : MvPolynomial σ R)

/-- Actual coefficient homomorphism into the degree-zero homogeneous component. -/
@[expose] def coeffZero : R →+* (Grading R σ 0) where
  toFun r := ⟨C r,isHomogeneous_C _ r⟩
  map_one' := Subtype.ext (map_one C)
  map_mul' a b := Subtype.ext (map_mul C a b)
  map_zero' := Subtype.ext (map_zero C)
  map_add' a b := Subtype.ext (map_add C a b)

@[expose] def coeff : R →+* Chart R σ j :=
  (fromZeroRingHom (Grading R σ) _).comp (coeffZero R σ)
instance chartAlgebra : Algebra R (Chart R σ j) := (coeff R σ j).toAlgebra

lemma val_coeff (r : R) : (coeff R σ j r).val=algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (C r) := by
  change Localization.mk (C r) 1=_
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_one (FullLocalization R σ j) (C r)

@[expose] def valAlgHom : Chart R σ j →ₐ[R] FullLocalization R σ j where
  __ := algebraMap (Chart R σ j) (FullLocalization R σ j)
  commutes' r := val_coeff R σ j r

@[expose] def coordinate (i : {i : σ // i ≠ j}) : Chart R σ j :=
  Away.mk (Grading R σ) (isHomogeneous_X R j) 1 (X (i:σ)) (by
    simpa using isHomogeneous_X R (i:σ))

@[expose] def toChart : MvPolynomial {i : σ // i ≠ j} R →ₐ[R] Chart R σ j := aeval (coordinate R σ j)

@[expose] def dehomogenize : MvPolynomial σ R →ₐ[R] MvPolynomial {i : σ // i ≠ j} R :=
  aeval (fun i => if h : i=j then 1 else X ⟨i,h⟩)
@[simp] theorem dehomogenize_at : dehomogenize R σ j (X j)=1 := by simp [dehomogenize]
@[simp] theorem dehomogenize_other (i : {i : σ // i ≠ j}) : dehomogenize R σ j (X (i:σ))=X i := by simp [dehomogenize,i.property]
@[simp] theorem dehomogenize_C (r : R) : dehomogenize R σ j (C r)=C r := by simp [dehomogenize]

@[expose] def fullEval : FullLocalization R σ j →ₐ[R] MvPolynomial {i : σ // i ≠ j} R :=
  IsLocalization.Away.liftAlgHom (f := dehomogenize R σ j) (X j) (by simp)

@[expose] def fromChart : Chart R σ j →ₐ[R] MvPolynomial {i : σ // i ≠ j} R :=
  (fullEval R σ j).comp (valAlgHom R σ j)

lemma fromChart_mk (n : ℕ) (p : MvPolynomial σ R) (hp : p ∈ Grading R σ (n • 1)) :
    fromChart R σ j (Away.mk (Grading R σ) (isHomogeneous_X R j) n p hp)=dehomogenize R σ j p := by
  change fullEval R σ j (Localization.mk p ⟨X j^n,by exact ⟨n,rfl⟩⟩)=_
  change Localization.awayLift (dehomogenize R σ j).toRingHom (X j)
    (by simp) (Localization.mk p ⟨X j^n,⟨n,rfl⟩⟩)=_
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp


@[simp] theorem fromChart_variable (i : {i : σ // i ≠ j}) : fromChart R σ j (coordinate R σ j i)=X i := by
  rw [coordinate,fromChart_mk,dehomogenize_other]

lemma fromChart_toChart : (fromChart R σ j).comp (toChart R σ j)=AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [toChart]

@[expose] def inverseCoordinate : FullLocalization R σ j := IsLocalization.Away.invSelf (S := FullLocalization R σ j) (X j : MvPolynomial σ R)
@[simp] theorem coordinate_inverse :
    algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (X j)*inverseCoordinate R σ j=1 :=
  IsLocalization.Away.mul_invSelf (S := FullLocalization R σ j) (X j : MvPolynomial σ R)

lemma val_coordinate (i : {i : σ // i ≠ j}) : (coordinate R σ j i).val=
    algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (X (i:σ))*inverseCoordinate R σ j := by
  change Localization.mk (X (i:σ)) ⟨X j^1,_⟩=_
  simp only [pow_one]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  rfl

lemma evaluation_diagram : ((valAlgHom R σ j).comp (toChart R σ j)).comp (dehomogenize R σ j)=
    aeval (fun i : σ => inverseCoordinate R σ j*
      algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (X i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i=j
  · subst i
    simp only [AlgHom.comp_apply,dehomogenize_at,map_one,aeval_X]
    exact (mul_comm _ _).trans (coordinate_inverse R σ j) |>.symm
  · have hd : dehomogenize R σ j (X i)=X (⟨i,hi⟩ : {i : σ // i ≠ j}) := by
      simp [dehomogenize,hi]
    simp only [AlgHom.comp_apply,hd,toChart,aeval_X]
    change (coordinate R σ j ⟨i,hi⟩).val=_
    rw [val_coordinate,mul_comm]

lemma val_mk (n : ℕ) (p : MvPolynomial σ R) (hp : p ∈ Grading R σ (n • 1)) :
    (Away.mk (Grading R σ) (isHomogeneous_X R j) n p hp).val=
      algebraMap (MvPolynomial σ R) (FullLocalization R σ j) p*(inverseCoordinate R σ j)^n := by
  change Localization.mk p ⟨X j^n,_⟩=_
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  change IsLocalization.mk' (FullLocalization R σ j) 1
    ((⟨X j,Submonoid.mem_powers _⟩ : Submonoid.powers (X j))^n)=_
  rw [←one_pow n,IsLocalization.mk'_pow]
  rfl

lemma toChart_fromChart [Fintype σ] : (toChart R σ j).comp (fromChart R σ j)=AlgHom.id _ _ := by
  apply AlgHom.ext
  intro q
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (Grading R σ) (isHomogeneous_X R j) q
  simp only [AlgHom.comp_apply,AlgHom.id_apply,fromChart_mk]
  apply HomogeneousLocalization.val_injective
  rw [val_mk]
  have he := AlgHom.congr_fun (evaluation_diagram R σ j) p
  change (toChart R σ j (dehomogenize R σ j p)).val=
    p.eval₂ (algebraMap R (FullLocalization R σ j)) (fun i => inverseCoordinate R σ j*
      algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (X i)) at he
  rw [he,eval_scaled _ _ n (by simpa using hp)]
  have hmap : (aeval (fun i : σ =>
      algebraMap (MvPolynomial σ R) (FullLocalization R σ j) (X i)))=
      Algebra.algHom R (MvPolynomial σ R) (FullLocalization R σ j) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [aeval_X]
    rfl
  change (inverseCoordinate R σ j)^n * (aeval _ p)=_
  rw [hmap]
  exact mul_comm _ _

/-- The actual homogeneous basic chart of Proj is the affine polynomial algebra. -/
@[expose] def chartEquiv [Fintype σ] : Chart R σ j ≃ₐ[R] MvPolynomial {i : σ // i ≠ j} R :=
  AlgEquiv.ofAlgHom (fromChart R σ j) (toChart R σ j) (fromChart_toChart R σ j) (toChart_fromChart R σ j)

end ProjectiveChart318
