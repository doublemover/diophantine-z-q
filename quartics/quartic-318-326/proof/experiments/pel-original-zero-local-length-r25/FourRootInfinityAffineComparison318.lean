module
public import FourRootReciprocalBranchData318
public section
noncomputable section
namespace FourRootInfinityAffineComparison318
open FourRootReciprocalBranchData318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
abbrev A:=FourRootAffineCoordinateRing318.Ring (branches b)
abbrev iz:=FourRootInfinityCoordinateRing318.coordinate b
abbrev az:=FourRootAffineCoordinateRing318.coordinate (branches b)

@[expose] def ratio:Fin 4→A b:=
  Fin.cases 1 (fun k=>algebraMap ℂ (A b) (scale b k)*az b (some k.succ))
lemma base_square:az b (some 0)^2=az b none:=by
  simpa only [branches_zero,map_zero,sub_zero] using
    FourRootAffineCoordinateRing318.relation (branches b) 0
lemma ratio_square (k:Fin 4):ratio b k^2=
    1+algebraMap ℂ (A b) (b 0-b k)*az b (some 0)^2:=by
  refine Fin.cases ?_ (fun j=>?_) k
  · simp [ratio]
  · change (algebraMap ℂ (A b) (scale b j)*az b (some j.succ))^2=_
    rw [mul_pow,←map_pow,scale_square,FourRootAffineCoordinateRing318.relation,
      branches_succ,map_neg,sub_neg_eq_add,base_square]
    have hd:algebraMap ℂ (A b) (difference b j)*algebraMap ℂ (A b) ((difference b j)⁻¹)=1:=by
      rw [←map_mul,mul_inv_cancel₀ (difference_ne_zero b hb j),map_one]
    change algebraMap ℂ (A b) (difference b j)*
      (az b none+algebraMap ℂ (A b) ((difference b j)⁻¹))=
        1+algebraMap ℂ (A b) (difference b j)*az b none
    linear_combination hd

/-- Entire normalized infinity ring, with all eight u=0 points, mapped
to a genuine finite four-root chart over the ACTUAL v=u² base. -/
@[expose] def toAffine:I b→ₐ[ℂ]A b:=
  FourRootInfinityCoordinateRing318.lift b (az b (some 0)) (ratio b) rfl (ratio_square b hb)
@[simp] lemma toAffine_u:toAffine b hb (iz b none)=az b (some 0):=
  FourRootInfinityCoordinateRing318.lift_coordinate ..
@[simp] lemma toAffine_ratio (k:Fin 4):toAffine b hb (iz b (some k))=ratio b k:=
  FourRootInfinityCoordinateRing318.lift_coordinate ..

@[expose] def root:Fin 4→I b:=
  Fin.cases (iz b none) (fun k=>algebraMap ℂ (I b) ((scale b k)⁻¹)*iz b (some k.succ))
lemma root_square (k:Fin 4):root b k^2=iz b none^2-algebraMap ℂ (I b) (branches b k):=by
  refine Fin.cases ?_ (fun j=>?_) k
  · simp [root,branches_zero]
  · change (algebraMap ℂ (I b) ((scale b j)⁻¹)*iz b (some j.succ))^2=_
    rw [mul_pow,←map_pow,inv_scale_square,FourRootInfinityCoordinateRing318.relation,
      branches_succ,map_neg,sub_neg_eq_add]
    have hd:algebraMap ℂ (I b) ((difference b j)⁻¹)*algebraMap ℂ (I b) (difference b j)=1:=by
      rw [←map_mul,inv_mul_cancel₀ (difference_ne_zero b hb j),map_one]
    change algebraMap ℂ (I b) ((difference b j)⁻¹)*
      (1+algebraMap ℂ (I b) (difference b j)*iz b none^2)=
        iz b none^2+algebraMap ℂ (I b) ((difference b j)⁻¹)
    linear_combination iz b none^2*hd
@[expose] def fromAffine:A b→ₐ[ℂ]I b:=
  FourRootAffineCoordinateRing318.lift (branches b) (iz b none^2) (root b) (root_square b hb)
@[simp] lemma fromAffine_base:fromAffine b hb (az b none)=iz b none^2:=
  FourRootAffineCoordinateRing318.lift_coordinate ..
@[simp] lemma fromAffine_root (k:Fin 4):fromAffine b hb (az b (some k))=root b k:=
  FourRootAffineCoordinateRing318.lift_coordinate ..

lemma from_to:(fromAffine b hb).comp (toAffine b hb)=AlgHom.id ℂ (I b):=by
  apply FourRootInfinityCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>simp [root]
  | some k=>
    refine Fin.cases ?_ (fun j=>?_) k
    · simp [ratio,FourRootInfinityCoordinateRing318.zero_relation]
    · simp only [AlgHom.comp_apply,toAffine_ratio,ratio,Fin.cases_succ,map_mul,
        AlgHom.commutes,fromAffine_root,root]
      rw [←mul_assoc,←map_mul,mul_inv_cancel₀ (scale_ne_zero b hb j),map_one,one_mul]
lemma to_from:(toAffine b hb).comp (fromAffine b hb)=AlgHom.id ℂ (A b):=by
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>simp [base_square]
  | some k=>
    refine Fin.cases ?_ (fun j=>?_) k
    · simp [root]
    · simp only [AlgHom.comp_apply,fromAffine_root,root,Fin.cases_succ,map_mul,
        AlgHom.commutes,toAffine_ratio,ratio]
      rw [←mul_assoc,←map_mul,inv_mul_cancel₀ (scale_ne_zero b hb j),map_one,one_mul]
@[expose] def equivalence:I b≃ₐ[ℂ]A b:=
  AlgEquiv.ofAlgHom (toAffine b hb) (fromAffine b hb) (to_from b hb) (from_to b hb)

lemma original_base (p:Polynomial ℂ):
    equivalence b hb (Polynomial.aeval (iz b none^2) p)=Polynomial.aeval (az b none) p:=by
  have h:(toAffine b hb).comp (Polynomial.aeval (iz b none^2))=
      Polynomial.aeval (az b none):=by
    apply Polynomial.algHom_ext
    simp [base_square]
  exact AlgHom.congr_fun h p

/-- The equivalence is over the literal original reciprocal projective
coordinate, not merely an abstract complex-algebra isomorphism. -/
@[expose] def polynomialEquivalence:
    letI:Algebra (Polynomial ℂ) (I b):=(Polynomial.aeval (iz b none^2)).toAlgebra
    letI:Algebra (Polynomial ℂ) (A b):=(Polynomial.aeval (az b none)).toAlgebra
    I b≃ₐ[Polynomial ℂ]A b:=
  { (equivalence b hb).toRingEquiv with commutes':=original_base b hb }
end FourRootInfinityAffineComparison318
