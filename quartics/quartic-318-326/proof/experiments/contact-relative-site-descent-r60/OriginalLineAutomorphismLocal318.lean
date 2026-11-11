module
public import LineFrameGauge318
public import LineFrameIsoTransport318
public import LineSheafClass318
public section
noncomputable section
namespace OriginalLineAutomorphismLocal318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L : Line X) (f : L.object ≅ L.object)

/-- The actual coordinate unit of an actual original line automorphism,
on every subopen of its original frame cover. -/
@[expose] def localScalar (i : L.Index) (W : X.Opens) (h : W ≤ L.opens i) : Γ(X,W)ˣ :=
  FrameScalarAlgebra318.scalar
    (OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) W h)
    (OpenLineFrameCoordinates318.frame L.object (L.opens i)
      (LineFrameIsoTransport318.transported f (L.opens i) (L.frame i)) W h)

lemma localScalar_action (i : L.Index) (W : X.Opens) (h : W ≤ L.opens i)
    (s : Γ(L.object,W)) : f.hom.app W s = (localScalar L f i W h).val • s := by
  let e := OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) W h
  obtain ⟨x, rfl⟩ := e.surjective s
  have hr := FrameScalarAlgebra318.relation e
    (OpenLineFrameCoordinates318.frame L.object (L.opens i)
      (LineFrameIsoTransport318.transported f (L.opens i) (L.frame i)) W h) x
  rw [LineFrameIsoTransport318.coordinates] at hr
  calc
    f.hom.app W (e x) = e ((localScalar L f i W h).val * x) := hr.symm
    _ = (localScalar L f i W h).val • e x := e.map_smul _ _

lemma localScalar_unique (i : L.Index) (W : X.Opens) (h : W ≤ L.opens i)
    (a : Γ(X,W)ˣ) (ha : ∀ s : Γ(L.object,W), f.hom.app W s = a.val • s) :
    localScalar L f i W h = a := by
  apply Units.ext
  let e := OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) W h
  have hx := (localScalar_action L f i W h (e 1)).symm.trans (ha (e 1))
  have he := congrArg e.symm hx
  simpa only [map_smul, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one] using he

/-- Scalar coordinates are independent of the frame on every common
subopen, not only on geometric points or a selected affine chart. -/
lemma localScalar_independent (i j : L.Index) (W : X.Opens)
    (hi : W ≤ L.opens i) (hj : W ≤ L.opens j) :
    localScalar L f i W hi = localScalar L f j W hj :=
  localScalar_unique L f i W hi _ (localScalar_action L f j W hj)

lemma localScalar_restrict (i : L.Index) (W : X.Opens) (h : W ≤ L.opens i) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
        (localScalar L f i (L.opens i) le_rfl) = localScalar L f i W h :=
  LineFrameGauge318.restrict L.object L.opens
    (fun i => LineFrameIsoTransport318.transported f (L.opens i) (L.frame i))
    L.frame i W h

lemma localScalars_compatible : TopCat.Presheaf.IsCompatible
    (StructureUnitsSheaf318.units X).obj L.opens
      (fun i => localScalar L f i (L.opens i) le_rfl) := by
  intro i j
  change Units.map (X.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom
      (localScalar L f i (L.opens i) le_rfl) =
    Units.map (X.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom
      (localScalar L f j (L.opens j) le_rfl)
  rw [localScalar_restrict, localScalar_restrict]
  exact localScalar_independent L f i j _ _ _
end OriginalLineAutomorphismLocal318
