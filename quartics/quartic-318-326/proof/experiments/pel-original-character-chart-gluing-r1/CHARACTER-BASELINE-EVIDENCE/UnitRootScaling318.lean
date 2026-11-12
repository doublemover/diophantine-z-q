module
public import ContactGenericFiber318
public section
noncomputable section
namespace UnitRootScaling318
open QuadraticPresentation318
set_option maxHeartbeats 600000
variable {R:Type*} [CommRing R]
@[expose] def hom (a b:R) (u:Rˣ) (h:a=b*(u:R)^2):RootRing a→ₐ[R]RootRing b:=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (RootRing b) (u:R)*AdjoinRoot.root (polynomial b)) (by
      change Polynomial.aeval _ (Polynomial.X^2-Polynomial.C a)=0
      simp only [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C,mul_pow,root_square]
      rw [h,map_mul,map_pow]
      ring)
@[simp] lemma hom_root (a b:R) (u:Rˣ) (h:a=b*(u:R)^2):
    hom a b u h (AdjoinRoot.root (polynomial a))=
      algebraMap R (RootRing b) (u:R)*AdjoinRoot.root (polynomial b):=
  AdjoinRoot.liftAlgHom_root _ _ _ _
lemma inverse_relation (a b:R) (u:Rˣ) (h:a=b*(u:R)^2):b=a*(↑u⁻¹:R)^2:=by
  rw [h]
  rw [mul_assoc,←mul_pow,Units.mul_inv,one_pow,mul_one]
@[expose] def equiv (a b:R) (u:Rˣ) (h:a=b*(u:R)^2):RootRing a≃ₐ[R]RootRing b:=
  AlgEquiv.ofAlgHom (hom a b u h) (hom b a u⁻¹ (inverse_relation a b u h))
    (by
      apply AdjoinRoot.algHom_ext
      change hom a b u h (hom b a u⁻¹ (inverse_relation a b u h) (AdjoinRoot.root (polynomial b)))=_
      rw [hom_root,map_mul,AlgHom.commutes,hom_root,←mul_assoc,←map_mul,
        Units.inv_mul,map_one,one_mul]
      rfl)
    (by
      apply AdjoinRoot.algHom_ext
      change hom b a u⁻¹ (inverse_relation a b u h) (hom a b u h (AdjoinRoot.root (polynomial a)))=_
      rw [hom_root,map_mul,AlgHom.commutes,hom_root,←mul_assoc,←map_mul,
        Units.mul_inv,map_one,one_mul]
      rfl)
end UnitRootScaling318
