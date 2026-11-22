module

public import SelectedActualLiteralMarkedGenericTensor318
public import SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
import all SelectedActualLiteralComplexCompactStalkDVR318
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

public section
noncomputable section

open Polynomial
open scoped Polynomial TensorProduct
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra literalWholeTensor literalWholeTensor_root)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318 (pC OrdinaryRoot intoGeneric intoWhole)

namespace SelectedActualMarkedTensorOrdinaryIntoWhole318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

/-- The ordinary germ field map transports the actual old coefficient.
The target algebra is the one used by the existing tensor equivalence. -/
theorem intoWhole_coefficient (a : Base) :
    letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
    intoWhole N p (AdjoinRoot.of (pC N p) a) = algebraMap Base (K N p) a := by
  letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  have hG : intoGeneric N p (AdjoinRoot.of (pC N p) a) =
      AdjoinRoot.of (P N p) (algebraMap Base Generic a) := by
    unfold intoGeneric
    exact AdjoinRoot.map_of _ _ _ _ _
  unfold intoWhole
  rw [RingHom.comp_apply,hG]
  change wholeRootEquiv N p (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) =
    AdjoinRoot.of (pJ N p) (algebraMap Base (RatFunc ℂ) a)
  change AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
    (pJ_associated N p).symm.dvd (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) = _
  exact (AdjoinRoot.map_of _ _ _ _ _).trans
    (congrArg (AdjoinRoot.of (pJ N p)) (ratEquiv.commutes a))

/-- The exact root in the ordinary germ map is the root of the same
whole polynomial defining the installed generic field. -/
theorem intoWhole_root :
    intoWhole N p (AdjoinRoot.root (pC N p)) = AdjoinRoot.root (pJ N p) := by
  have hG : intoGeneric N p (AdjoinRoot.root (pC N p)) = AdjoinRoot.root (P N p) := by
    unfold intoGeneric
    exact AdjoinRoot.map_root _ _ _ _
  unfold intoWhole
  rw [RingHom.comp_apply,hG]
  exact wholeRootEquiv_root N p

/-- The generic map built by tensorizing the same complex ordinary marked
polynomial quotient is literally the map used to read meromorphic germs.
There is no new algebra or scalar tower to supply. -/
theorem literalWholeTensor_eq_intoWhole (z : OrdinaryRoot N p) :
    letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
    literalWholeTensor N p (z ⊗ₜ[Base] (1 : Generic)) = intoWhole N p z := by
  letI : Algebra Base (K N p) := ordinaryFieldAlgebra N p
  let C := OrdinaryRoot N p
  let T := C ⊗[Base] Generic
  let E : T ≃ₐ[Base] K N p := literalWholeTensor N p
  let i : C →ₐ[Base] T := Algebra.TensorProduct.includeLeft
  have hi (u : C) : i u = u ⊗ₜ[Base] (1 : Generic) :=
    Algebra.TensorProduct.includeLeft_apply u
  let f : C →ₐ[Base] K N p := {
    intoWhole N p with
    commutes' := fun a => by
      rw [AdjoinRoot.algebraMap_eq]
      exact intoWhole_coefficient N p a }
  have h : E.toAlgHom.comp i = f := by
    apply AdjoinRoot.algHom_ext
    change E (i (AdjoinRoot.root (pC N p))) = intoWhole N p (AdjoinRoot.root (pC N p))
    rw [hi]
    exact (literalWholeTensor_root N p).trans (intoWhole_root N p).symm
  have hz : E (i z) = intoWhole N p z := DFunLike.congr_fun h z
  exact (congrArg E (hi z)).symm.trans hz

end SelectedActualMarkedTensorOrdinaryIntoWhole318

#print axioms SelectedActualMarkedTensorOrdinaryIntoWhole318.intoWhole_coefficient
#print axioms SelectedActualMarkedTensorOrdinaryIntoWhole318.intoWhole_root
#print axioms SelectedActualMarkedTensorOrdinaryIntoWhole318.literalWholeTensor_eq_intoWhole
