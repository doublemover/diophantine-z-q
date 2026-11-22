module

public import SelectedActualLiteralComplexCompactStalkDVR318
public import SelectedMonicReducedFiber318
import all SelectedActualLiteralComplexCompactStalkDVR318
import all SelectedMonicReducedFiber318

public section
noncomputable section

open scoped TensorProduct Polynomial
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualComplexOrdinaryScalar318
open SelectedActualLiteralComplexCompactStalkDVR318 SelectedMonicReducedFiber318

namespace SelectedActualLiteralMarkedGenericTensor318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev pC := p.map (toComplex N)
abbrev C := AdjoinRoot (pC N p)

/-- The literal ordinary scalar map into the verified whole marked
field, rather than an independently supplied Base-algebra. -/
@[expose] def ordinaryFieldAlgebra : Algebra Base (K N p) :=
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  Algebra.compHom (K N p) (algebraMap Base (RatFunc ℂ))

private theorem whole_comparison_on_base (a : Base) :
    letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
    wholeRootEquiv N p (algebraMap Base (AdjoinRoot (P N p)) a) =
      algebraMap Base (K N p) a := by
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
  change wholeRootEquiv N p (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) =
    AdjoinRoot.of (pJ N p) (algebraMap Base (RatFunc ℂ) a)
  change AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
    (pJ_associated N p).symm.dvd
      (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) = _
  have hOf : AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
      (pJ_associated N p).symm.dvd
        (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) =
          AdjoinRoot.of (pJ N p) (ratEquiv (algebraMap Base Generic a)) :=
    AdjoinRoot.map_of _ _ _ _ _
  exact hOf.trans (congrArg (AdjoinRoot.of (pJ N p)) (ratEquiv.commutes a))

/-- The full ordinary root algebra tensored with the base fraction
field is the exact original installed whole field. Every map uses the
same p; the root is not chosen again. -/
def literalWholeTensor :
    letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
    (C N p ⊗[Base] Generic) ≃ₐ[Base] K N p := by
  letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
  let W : AdjoinRoot (P N p) ≃ₐ[Base] K N p :=
    { wholeRootEquiv N p with commutes' := whole_comparison_on_base N p }
  exact ((Algebra.TensorProduct.comm Base (C N p) Generic).trans
    ((mappedRootEquiv Generic (pC N p)).restrictScalars Base)).trans W

private theorem mapAlgEquiv_at_root {A T U : Type*}
    [CommRing A] [CommRing T] [CommRing U] [Algebra A T] [Algebra A U]
    (v : T ≃ₐ[A] U) (q : T[X]) (r : U[X])
    (hr : Associated (q.map v) r) :
    AdjoinRoot.mapAlgEquiv v q r hr (AdjoinRoot.root q) = AdjoinRoot.root r := by
  change AdjoinRoot.map (v : T →+* U) q r hr.symm.dvd (AdjoinRoot.root q) = _
  exact AdjoinRoot.map_root _ _ _ _

theorem literalWholeTensor_root :
    letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
    literalWholeTensor N p (AdjoinRoot.root (pC N p) ⊗ₜ[Base] (1 : Generic)) =
      AdjoinRoot.root (pJ N p) := by
  letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
  let e : Generic ⊗[Base] C N p ≃ₐ[Generic] AdjoinRoot (P N p) :=
    mappedRootEquiv Generic (pC N p)
  have hx : e ((1 : Generic) ⊗ₜ[Base] AdjoinRoot.root (pC N p)) =
      AdjoinRoot.root (P N p) := by
    unfold e mappedRootEquiv
    rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
    exact mapAlgEquiv_at_root _ _ _ _
  unfold literalWholeTensor
  change wholeRootEquiv N p
    (e ((Algebra.TensorProduct.comm Base (C N p) Generic)
      (AdjoinRoot.root (pC N p) ⊗ₜ[Base] (1 : Generic)))) = _
  rw [Algebra.TensorProduct.comm_tmul,hx]
  exact wholeRootEquiv_root N p

end SelectedActualLiteralMarkedGenericTensor318

#print axioms SelectedActualLiteralMarkedGenericTensor318.literalWholeTensor_root
