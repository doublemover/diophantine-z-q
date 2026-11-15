module
public import FourRootActionStabilizers318
public import FourRootActualGenericField318
public section
noncomputable section
namespace FourRootActualGenericSigns318
open FourBinaryCharacters318 FourRootAffineTensorPresentation318 FourRootOrderSigns318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)

lemma sign_scalar {S:Type*} [CommRing S] [Algebra ℂ S] (i:Fin 4) (z:S):
    (if signPattern g i then -z else z)=algebraMap ℂ S (coordinate (F:=ℂ) i g)*z:=by
  by_cases h:Multiplicative.toAdd (g i)=0
  · simp [signPattern,coordinate,h]
  · simp [signPattern,coordinate,h]

/-- The independently defined affine ring action is exactly the original
quadratic-tensor sign action under the coefficient-preserving equivalence. -/
lemma tensor_equivariant (x:FourRootAffineCoordinateRing318.Ring b):
    equivalence b (FourRootCoordinateRingSigns318.finiteEnd b g x)=
      signEquiv (radicand b) (signPattern g) (equivalence b x):=by
  have he: (equivalence b).toAlgHom.comp (FourRootCoordinateRingSigns318.finiteEnd b g)=
      ((signEquiv (radicand b) (signPattern g)).toAlgHom.restrictScalars ℂ).comp
        (equivalence b).toAlgHom:=by
    apply FourRootAffineCoordinateRing318.hom_ext
    intro k
    cases k with
    | none=>
      change toTensor b (FourRootCoordinateRingSigns318.finiteEnd b g
        (FourRootAffineCoordinateRing318.coordinate b none))=_
      rw [FourRootCoordinateRingSigns318.finite_base,toTensor_base]
      exact (AlgEquiv.commutes _ _).symm
    | some i=>
      change toTensor b (FourRootCoordinateRingSigns318.finiteEnd b g
        (FourRootAffineCoordinateRing318.coordinate b (some i)))=
        signEquiv (radicand b) (signPattern g)
          (toTensor b (FourRootAffineCoordinateRing318.coordinate b (some i)))
      rw [FourRootCoordinateRingSigns318.finite_root,map_mul,AlgHom.commutes,
        toTensor_root,signEquiv_generator,sign_scalar]
  exact AlgHom.congr_fun he x

/-- This is an automorphism of the ENTIRE actual generic tensor field,
not merely a permutation of selected complex points. -/
@[expose] def genericAutomorphism:
    KummerTensorField318.Raw (FourRootActualGenericField318.parameter b)≃ₐ[FourRootActualGenericField318.K]
      KummerTensorField318.Raw (FourRootActualGenericField318.parameter b):=
  signEquiv (FourRootActualGenericField318.parameter b) (signPattern g)

lemma embedding_equivariant (x:TensorRing b):
    FourRootActualGenericField318.embedding b (signEquiv (radicand b) (signPattern g) x)=
      genericAutomorphism b g (FourRootActualGenericField318.embedding b x):=by
  exact AlgHom.congr_fun
    (FourRootSignBaseChange318.sign_coefficientMap (radicand b)
      FourRootActualGenericField318.K (signPattern g)) x

/-- The literal affine coordinate ring, its full generic field and the
original analytic root signs are the SAME equivariant construction. -/
theorem affineEmbedding_equivariant (x:FourRootAffineCoordinateRing318.Ring b):
    FourRootActualGenericField318.affineEmbedding b
      (FourRootCoordinateRingSigns318.finiteEnd b g x)=
      genericAutomorphism b g (FourRootActualGenericField318.affineEmbedding b x):=by
  change FourRootActualGenericField318.embedding b
      (equivalence b (FourRootCoordinateRingSigns318.finiteEnd b g x))=_
  rw [tensor_equivariant,embedding_equivariant]
end FourRootActualGenericSigns318
