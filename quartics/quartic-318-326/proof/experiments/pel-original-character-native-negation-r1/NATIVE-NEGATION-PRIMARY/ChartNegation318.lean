module
public import AffineEquationFunctor318
public import WeierstrassGluing318
public section
noncomputable section
namespace ChartNegation318
open WeierstrassOverlap318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R]

/-- Actual finite-chart negation, (x,y)↦(x,-y). -/
@[expose] def affineNeg (A B:R) : Affine A B →ₐ[R] Affine A B :=
  AffineEquationFunctor318.toHom A B
    ⟨(ShortAffineJacobian318.x A B,-ShortAffineJacobian318.y A B),by
      linear_combination ShortAffineJacobian318.relation A B⟩
@[simp] theorem affineNeg_x (A B:R) : affineNeg A B (ShortAffineJacobian318.x A B)=
    ShortAffineJacobian318.x A B := AffineEquationFunctor318.toHom_x _ _ _
@[simp] theorem affineNeg_y (A B:R) : affineNeg A B (ShortAffineJacobian318.y A B)=
    -ShortAffineJacobian318.y A B := AffineEquationFunctor318.toHom_y _ _ _

theorem affineNeg_twice (A B:R) : (affineNeg A B).comp (affineNeg A B)=AlgHom.id R _ := by
  apply affine_hom_ext <;> simp

/-- Actual infinity-chart negation, (x,z)↦(-x,-z). -/
@[expose] def infinityNeg (A B:R) : Infinity A B →ₐ[R] Infinity A B :=
  InfinityChart318.lift A B (-InfinityChart318.x A B) (-InfinityChart318.z A B) (by
    linear_combination -InfinityChart318.relation A B)
@[simp] theorem infinityNeg_x (A B:R) : infinityNeg A B (InfinityChart318.x A B)=
    -InfinityChart318.x A B := InfinityChart318.lift_x _ _ _ _ _
@[simp] theorem infinityNeg_z (A B:R) : infinityNeg A B (InfinityChart318.z A B)=
    -InfinityChart318.z A B := InfinityChart318.lift_z _ _ _ _ _

theorem infinityNeg_twice (A B:R) : (infinityNeg A B).comp (infinityNeg A B)=AlgHom.id R _ := by
  apply InfinityChart318.hom_ext <;> simp

/-- Actual localized overlap involution. -/
@[expose] def overlapNeg (A B:R) : InfinityOverlap A B →ₐ[R] InfinityOverlap A B :=
  IsLocalization.Away.liftAlgHom
    (f:=(IsScalarTower.toAlgHom R (Infinity A B) (InfinityOverlap A B)).comp (infinityNeg A B))
    (InfinityChart318.z A B) (by
      simp only [AlgHom.comp_apply,infinityNeg_z,map_neg]
      exact (IsLocalization.Away.algebraMap_isUnit (S:=InfinityOverlap A B)
        (InfinityChart318.z A B)).neg)

@[simp] theorem overlapNeg_map (A B:R) (a:Infinity A B) :
    overlapNeg A B (algebraMap (Infinity A B) (InfinityOverlap A B) a)=
      algebraMap (Infinity A B) (InfinityOverlap A B) (infinityNeg A B a) := by
  simp [overlapNeg,IsLocalization.Away.liftAlgHom_apply]
@[simp] theorem overlapNeg_ix (A B:R) : overlapNeg A B (ix A B)= -ix A B := by
  simp [ix]
@[simp] theorem overlapNeg_iz (A B:R) : overlapNeg A B (iz A B)= -iz A B := by
  simp [iz]
@[simp] theorem overlapNeg_ii (A B:R) : overlapNeg A B (ii A B)= -ii A B := by
  have hh:=congrArg (overlapNeg A B) (iz_ii A B)
  simp only [map_mul,map_one,overlapNeg_iz] at hh
  calc
    _ = ii A B*(iz A B*overlapNeg A B (ii A B)) := by
      rw [←mul_assoc,mul_comm (ii A B),iz_ii,one_mul]
    _ = ii A B*(-1) := by congr 1; linear_combination -hh
    _ = -ii A B := by ring

/-- Compatibility with the actual nontrivial chart transition. -/
theorem affine_overlap (A B:R) :
    (overlapNeg A B).comp (toInfinityBase A B)=
      (toInfinityBase A B).comp (affineNeg A B) := by
  apply affine_hom_ext
  · simp
  · simp

/-- Compatibility with the actual infinity localization map. -/
theorem infinity_overlap (A B:R) :
    (overlapNeg A B).comp (IsScalarTower.toAlgHom R (Infinity A B) (InfinityOverlap A B))=
      (IsScalarTower.toAlgHom R (Infinity A B) (InfinityOverlap A B)).comp (infinityNeg A B) := by
  apply AlgHom.ext
  intro a
  exact overlapNeg_map A B a

end ChartNegation318
