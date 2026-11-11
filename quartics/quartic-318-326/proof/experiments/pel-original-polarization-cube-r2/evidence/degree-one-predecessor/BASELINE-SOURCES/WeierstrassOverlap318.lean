module
public import InfinityChart318
public import ShortAffineJacobian318
public section
noncomputable section
namespace WeierstrassOverlap318
open MvPolynomial Algebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

abbrev Affine (A B : R) := ShortAffineJacobian318.Ring A B
abbrev Infinity (A B : R) := InfinityChart318.Ring A B
abbrev AffineOverlap (A B : R) := Localization.Away (ShortAffineJacobian318.y A B)
abbrev InfinityOverlap (A B : R) := Localization.Away (InfinityChart318.z A B)

@[expose] def ax (A B : R) : AffineOverlap A B := algebraMap (Affine A B) _ (ShortAffineJacobian318.x A B)
@[expose] def ay (A B : R) : AffineOverlap A B := algebraMap (Affine A B) _ (ShortAffineJacobian318.y A B)
@[expose] def ai (A B : R) : AffineOverlap A B := IsLocalization.Away.invSelf (ShortAffineJacobian318.y A B)
@[expose] def ix (A B : R) : InfinityOverlap A B := algebraMap (Infinity A B) _ (InfinityChart318.x A B)
@[expose] def iz (A B : R) : InfinityOverlap A B := algebraMap (Infinity A B) _ (InfinityChart318.z A B)
@[expose] def ii (A B : R) : InfinityOverlap A B := IsLocalization.Away.invSelf (InfinityChart318.z A B)

@[simp] theorem ay_ai (A B : R) : ay A B*ai A B=1 := IsLocalization.Away.mul_invSelf _
@[simp] theorem iz_ii (A B : R) : iz A B*ii A B=1 := IsLocalization.Away.mul_invSelf _

lemma affine_relation (A B : R) : ay A B^2-ax A B^3-algebraMap R (AffineOverlap A B) A*ax A B-
    algebraMap R (AffineOverlap A B) B=0 := by
  have h := congrArg (algebraMap (Affine A B) (AffineOverlap A B)) (ShortAffineJacobian318.relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,←IsScalarTower.algebraMap_apply,ax,ay] using h

lemma infinity_relation (A B : R) : iz A B-ix A B^3-algebraMap R (InfinityOverlap A B) A*ix A B*iz A B^2-
    algebraMap R (InfinityOverlap A B) B*iz A B^3=0 := by
  have h := congrArg (algebraMap (Infinity A B) (InfinityOverlap A B)) (InfinityChart318.relation A B)
  simpa only [map_sub,map_pow,map_mul,map_zero,←IsScalarTower.algebraMap_apply,ix,iz] using h

section AffineLift
variable {S : Type*} [CommRing S] [Algebra R S]
@[expose] def affineLift (A B : R) (a b : S) (h : b^2-a^3-algebraMap R S A*a-algebraMap R S B=0) :
    Affine A B →ₐ[R] S := by
  let e : MvPolynomial (Fin 2) R →ₐ[R] S := MvPolynomial.aeval ![a,b]
  have hk : Ideal.span (Set.range (ShortAffineJacobian318.equations A B)) ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change e (ShortAffineJacobian318.equation A B)=0
    simpa [e,ShortAffineJacobian318.equation] using h
  exact Ideal.Quotient.liftₐ _ e (fun f hf => hk hf)

@[simp] theorem affineLift_x (A B : R) (a b : S) (h) :
    affineLift A B a b h (ShortAffineJacobian318.x A B)=a := by
  simp [affineLift,ShortAffineJacobian318.x,Ideal.Quotient.liftₐ_apply]
@[simp] theorem affineLift_y (A B : R) (a b : S) (h) :
    affineLift A B a b h (ShortAffineJacobian318.y A B)=b := by
  simp [affineLift,ShortAffineJacobian318.y,Ideal.Quotient.liftₐ_apply]
@[ext] theorem affine_hom_ext (A B : R) {f g : Affine A B →ₐ[R] S}
    (hx : f (ShortAffineJacobian318.x A B)=g (ShortAffineJacobian318.x A B))
    (hy : f (ShortAffineJacobian318.y A B)=g (ShortAffineJacobian318.y A B)) : f=g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy
end AffineLift

/-- X/Y and Z/Y on the actual finite chart where Y is invertible. -/
@[expose] def toAffineBase (A B : R) : Infinity A B →ₐ[R] AffineOverlap A B :=
  InfinityChart318.lift A B (ax A B*ai A B) (ai A B) (by
    calc
      _ = ai A B^3*(ay A B^2-ax A B^3-algebraMap R (AffineOverlap A B) A*ax A B-
        algebraMap R (AffineOverlap A B) B)+ai A B*(1-(ay A B*ai A B)^2) := by ring
      _ = 0 := by rw [affine_relation,ay_ai]; ring)

/-- X/Z and Y/Z on the actual infinity chart where Z is invertible. -/
@[expose] def toInfinityBase (A B : R) : Affine A B →ₐ[R] InfinityOverlap A B :=
  affineLift A B (ix A B*ii A B) (ii A B) (by
    have h := infinity_relation A B
    have hz := iz_ii A B
    calc
      _ = ii A B^3*(iz A B-ix A B^3-algebraMap R (InfinityOverlap A B) A*ix A B*iz A B^2-
        algebraMap R (InfinityOverlap A B) B*iz A B^3)+
        (1-iz A B*ii A B)*(ii A B^2-algebraMap R (InfinityOverlap A B) A*ix A B*ii A B*(iz A B*ii A B+1)-
          algebraMap R (InfinityOverlap A B) B*((iz A B*ii A B)^2+iz A B*ii A B+1)) := by ring
      _ = 0 := by rw [h,hz]; ring)

@[simp] theorem toAffineBase_x (A B : R) : toAffineBase A B (InfinityChart318.x A B)=ax A B*ai A B := by
  exact InfinityChart318.lift_x ..
@[simp] theorem toAffineBase_z (A B : R) : toAffineBase A B (InfinityChart318.z A B)=ai A B := by
  exact InfinityChart318.lift_z ..
@[simp] theorem toInfinityBase_x (A B : R) : toInfinityBase A B (ShortAffineJacobian318.x A B)=ix A B*ii A B := by
  exact affineLift_x ..
@[simp] theorem toInfinityBase_y (A B : R) : toInfinityBase A B (ShortAffineJacobian318.y A B)=ii A B := by
  exact affineLift_y ..

@[expose] def toAffine (A B : R) : InfinityOverlap A B →ₐ[R] AffineOverlap A B :=
  IsLocalization.Away.liftAlgHom (f := toAffineBase A B) (InfinityChart318.z A B) (by
    rw [toAffineBase_z]
    exact IsUnit.of_mul_eq_one_right _ (ay_ai A B))
@[expose] def toInfinity (A B : R) : AffineOverlap A B →ₐ[R] InfinityOverlap A B :=
  IsLocalization.Away.liftAlgHom (f := toInfinityBase A B) (ShortAffineJacobian318.y A B) (by
    rw [toInfinityBase_y]
    exact IsUnit.of_mul_eq_one_right _ (iz_ii A B))

@[simp] theorem toAffine_map (A B : R) (a : Infinity A B) :
    toAffine A B (algebraMap (Infinity A B) (InfinityOverlap A B) a)=toAffineBase A B a := by
  simp [toAffine,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem toInfinity_map (A B : R) (a : Affine A B) :
    toInfinity A B (algebraMap (Affine A B) (AffineOverlap A B) a)=toInfinityBase A B a := by
  simp [toInfinity,IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem toAffine_ix (A B : R) : toAffine A B (ix A B)=ax A B*ai A B := by simp [ix]
@[simp] theorem toAffine_iz (A B : R) : toAffine A B (iz A B)=ai A B := by simp [iz]
@[simp] theorem toInfinity_ax (A B : R) : toInfinity A B (ax A B)=ix A B*ii A B := by simp [ax]
@[simp] theorem toInfinity_ay (A B : R) : toInfinity A B (ay A B)=ii A B := by simp [ay]

@[simp] theorem toAffine_ii (A B : R) : toAffine A B (ii A B)=ay A B := by
  have h := congrArg (toAffine A B) (iz_ii A B)
  simp only [map_mul,map_one,toAffine_iz] at h
  calc
    _ = (ay A B*ai A B)*toAffine A B (ii A B) := by rw [ay_ai,one_mul]
    _ = ay A B*(ai A B*toAffine A B (ii A B)) := by ring
    _ = ay A B := by rw [h,mul_one]
@[simp] theorem toInfinity_ai (A B : R) : toInfinity A B (ai A B)=iz A B := by
  have h := congrArg (toInfinity A B) (ay_ai A B)
  simp only [map_mul,map_one,toInfinity_ay] at h
  calc
    _ = (iz A B*ii A B)*toInfinity A B (ai A B) := by rw [iz_ii,one_mul]
    _ = iz A B*(ii A B*toInfinity A B (ai A B)) := by ring
    _ = iz A B := by rw [h,mul_one]

lemma inverse_left (A B : R) : (toInfinity A B).comp (toAffine A B)=AlgHom.id R (InfinityOverlap A B) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (InfinityChart318.z A B))
  apply InfinityChart318.hom_ext
  · change toInfinity A B (toAffine A B (ix A B))=ix A B
    simp only [toAffine_ix,map_mul,toInfinity_ax,toInfinity_ai]
    calc
      _ = ix A B*(iz A B*ii A B) := by ring
      _ = ix A B := by rw [iz_ii,mul_one]
  · change toInfinity A B (toAffine A B (iz A B))=iz A B
    simp
lemma inverse_right (A B : R) : (toAffine A B).comp (toInfinity A B)=AlgHom.id R (AffineOverlap A B) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (ShortAffineJacobian318.y A B))
  apply affine_hom_ext
  · change toAffine A B (toInfinity A B (ax A B))=ax A B
    simp only [toInfinity_ax,map_mul,toAffine_ix,toAffine_ii]
    calc
      _ = ax A B*(ay A B*ai A B) := by ring
      _ = ax A B := by rw [ay_ai,mul_one]
  · change toAffine A B (toInfinity A B (ay A B))=ay A B
    simp

/-- Exact actual overlap algebra equivalence of the two projective Weierstrass charts. -/
@[expose] def overlapEquiv (A B : R) : InfinityOverlap A B ≃ₐ[R] AffineOverlap A B :=
  AlgEquiv.ofAlgHom (toAffine A B) (toInfinity A B) (inverse_right A B) (inverse_left A B)

end WeierstrassOverlap318
