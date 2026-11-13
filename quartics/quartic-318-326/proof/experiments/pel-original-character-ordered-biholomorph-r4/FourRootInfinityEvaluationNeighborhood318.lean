module
public import FourRootCharacterInfinityOpen318
public import FourRootNormalizedOverlap318
public section
noncomputable section
namespace FourRootInfinityEvaluationNeighborhood318
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (k:Fin 3→Fin 4)
@[expose] def product (p:InfinityPoints b):ℂ:=p.val.2 (k 0)*p.val.2 (k 1)*p.val.2 (k 2)
abbrev Neighborhood:={p:InfinityPoints b//product b k p≠0}
@[expose] def evaluation (p:InfinityPoints b):FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]ℂ:=
  (FourRootInfinityCoordinateRing318.pointEquiv b).symm p
lemma evaluation_coordinate (p:InfinityPoints b) (j:Option (Fin 4)):
    evaluation b p (FourRootInfinityCoordinateRing318.coordinate b j)=
      Option.elim p.val.1 p.val.2 j:=by
  cases j <;> simp [evaluation,FourRootInfinityCoordinateRing318.pointEquiv]
lemma evaluation_denominator (p:InfinityPoints b):
    evaluation b p (FourRootCharacterInfinityOpen318.denominator b k)=product b k p:=by
  simp only [FourRootCharacterInfinityOpen318.denominator,map_mul,evaluation_coordinate,product,Option.elim_some]
@[expose] def lift (p:Neighborhood b k):FourRootCharacterInfinityOpen318.OpenRing b k→ₐ[ℂ]ℂ:=
  IsLocalization.Away.liftAlgHom (f:=evaluation b p.val)
    (FourRootCharacterInfinityOpen318.denominator b k)
    (isUnit_iff_ne_zero.mpr (by rw [evaluation_denominator];exact p.property))
lemma lift_on_ring (p:Neighborhood b k) (x:FourRootInfinityCoordinateRing318.Ring b):
    lift b k p (algebraMap _ (FourRootCharacterInfinityOpen318.OpenRing b k) x)=evaluation b p.val x:=by
  simp only [lift,IsLocalization.Away.liftAlgHom_apply]
lemma lift_u (p:Neighborhood b k):
    lift b k p (FourRootCharacterInfinityOpen318.u b k)=p.val.val.1:=by
  rw [FourRootCharacterInfinityOpen318.u,lift_on_ring,evaluation_coordinate]
  rfl
lemma lift_root (p:Neighborhood b k):
    lift b k p (FourRootCharacterInfinityOpen318.rootUnit b k)=product b k p.val:=by
  rw [FourRootCharacterInfinityOpen318.rootUnit_val,lift_on_ring,evaluation_denominator]
lemma lift_inverse (p:Neighborhood b k):
    lift b k p (↑(FourRootCharacterInfinityOpen318.rootUnit b k)⁻¹)=
      (product b k p.val)⁻¹:=by
  have hu:(FourRootCharacterInfinityOpen318.rootUnit b k:FourRootCharacterInfinityOpen318.OpenRing b k)*
      (↑(FourRootCharacterInfinityOpen318.rootUnit b k)⁻¹)=1:=
    congrArg (fun v:(FourRootCharacterInfinityOpen318.OpenRing b k)ˣ=>(v:FourRootCharacterInfinityOpen318.OpenRing b k))
      (mul_inv_cancel (FourRootCharacterInfinityOpen318.rootUnit b k))
  have h:=congrArg (lift b k p) hu
  simp only [map_mul,map_one,lift_root] at h
  exact mul_left_cancel₀ p.property (h.trans (mul_inv_cancel₀ p.property).symm)
lemma continuous_product:Continuous (product b k):=by unfold product;fun_prop
lemma neighborhood_open:IsOpen {p:InfinityPoints b|product b k p≠0}:=
  isOpen_ne (continuous_product b k) continuous_const
lemma contains_zero (p:InfinityPoints b) (hp:p.val.1=0):product b k p≠0:=by
  rw [←evaluation_denominator]
  apply FourRootCharacterInfinityOpen318.point_denominator_nonzero
  rw [evaluation_coordinate]
  exact hp
end FourRootInfinityEvaluationNeighborhood318
