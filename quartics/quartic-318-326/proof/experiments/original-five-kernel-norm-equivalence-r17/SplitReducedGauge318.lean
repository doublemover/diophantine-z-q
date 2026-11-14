module
public import OriginalLineIsoGauge318
public section
noncomputable section
namespace SplitReducedGauge318
open AlgebraicGeometry CategoryTheory Opposite UnitTransitionCocycle318
universe u
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Map the entire gauge equation before specializing presheaf carriers to
scheme structure units. The conclusion retains both full overlap restrictions. -/
private lemma mapped_gauge_restrictions {Z : TopCat.{u}} {κ : Type u}
    {F G : Z.Presheaf CommGrpCat.{u}} (φ : F ⟶ G) (U : κ → TopologicalSpace.Opens Z)
    (c d : Cocycle F U)
    (rc : ∀ k l, φ.app (op (U k ⊓ U l)) (c.transition k l) = 1)
    (rd : ∀ k l, φ.app (op (U k ⊓ U l)) (d.transition k l) = 1)
    (a : ∀ k, F.obj (op (U k)))
    (ha : ∀ k l, d.transition k l = coboundary F U a k l * c.transition k l)
    (k l : κ) :
    restrict G inf_le_left (φ.app (op (U k)) (a k)) =
      restrict G inf_le_right (φ.app (op (U l)) (a l)) := by
  have h := congrArg (fun z => φ.app (op (U k ⊓ U l)) z) (ha k l)
  rw [rd k l, map_mul, map_coboundary, rc k l, mul_one] at h
  exact mul_inv_eq_one.mp h.symm

variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (r : X ⟶ X₀) (hr : i ≫ r = 𝟙 X₀)
    {κ : Type u} (U : κ → X.Opens)
    (stable : ∀ k, U k ≤ r ⁻¹ᵁ (i ⁻¹ᵁ U k))
    (c d : Cocycle (StructureUnitsSheaf318.units X).obj U)
    (rc : UnitCocyclePointedLine318.ReducesToOne i U c)
    (rd : UnitCocyclePointedLine318.ReducesToOne i U d)
    (a : ∀ k, Γ(X,U k)ˣ)
    (ha : ∀ k l, d.transition k l = coboundary (StructureUnitsSheaf318.units X).obj U a k l * c.transition k l)
@[expose] def reduced (k : κ) : Γ(X₀,i ⁻¹ᵁ U k)ˣ := Units.map (i.app (U k)).hom.toMonoidHom (a k)
include rc rd ha in
lemma reduced_compatible (k l : κ) :
    Units.map (X₀.presheaf.map (homOfLE (i.preimage_mono (show U k ⊓ U l ≤ U k from inf_le_left))).op).hom.toMonoidHom
      (reduced i U a k) =
    Units.map (X₀.presheaf.map (homOfLE (i.preimage_mono (show U k ⊓ U l ≤ U l from inf_le_right))).op).hom.toMonoidHom
      (reduced i U a l) := by
  exact mapped_gauge_restrictions (Functor.whiskerRight i.c OpenUnitNorm318.unitsFunctor)
    U c d rc rd a ha k l
@[expose] def lifted (k : κ) : Γ(X,U k)ˣ :=
  SplitOpenUnitLift318.unitLift i r (U k) (stable k) (reduced i U a k)
include rc rd ha in
lemma lifted_compatible (k l : κ) :
    restrict (StructureUnitsSheaf318.units X).obj inf_le_left (lifted i r U stable a k) =
      restrict (StructureUnitsSheaf318.units X).obj inf_le_right (lifted i r U stable a l) := by
  let hkl : U k ⊓ U l ≤ r ⁻¹ᵁ (i ⁻¹ᵁ (U k ⊓ U l)) := inf_le_inf (stable k) (stable l)
  change Units.map (X.presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom
    (SplitOpenUnitLift318.unitLift i r (U k) (stable k) (reduced i U a k)) =
    Units.map (X.presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom
      (SplitOpenUnitLift318.unitLift i r (U l) (stable l) (reduced i U a l))
  rw [SplitOpenUnitLift318.unit_natural i r inf_le_left (stable k) hkl,
    SplitOpenUnitLift318.unit_natural i r inf_le_right (stable l) hkl,
    reduced_compatible i U c d rc rd a ha]
@[expose] def corrected (k : κ) : Γ(X,U k)ˣ := a k * (lifted i r U stable a k)⁻¹
include hr in
lemma corrected_reduces (k : κ) : Units.map (i.app (U k)).hom.toMonoidHom
    (corrected i r U stable a k) = 1 := by
  change Units.map (i.app (U k)).hom.toMonoidHom (a k *
    (SplitOpenUnitLift318.unitLift i r (U k) (stable k) (reduced i U a k))⁻¹) = 1
  rw [map_mul, map_inv, SplitOpenUnitLift318.reduction_unit i r hr]
  exact mul_inv_cancel _
include rc rd ha in
/-- Compatible lifted reductions have zero coboundary. Correcting by them
therefore leaves the ORIGINAL full gauge equation unchanged. -/
lemma corrected_equation (k l : κ) : d.transition k l =
    coboundary (StructureUnitsSheaf318.units X).obj U (corrected i r U stable a) k l * c.transition k l := by
  rw [ha k l]
  congr 1
  simp only [coboundary, corrected, map_mul, map_inv]
  rw [lifted_compatible i r U stable c d rc rd a ha k l]
  group
include stable hr rc rd ha in
/-- Every original gauge between reduced-to-one cocycles can itself be made
reduced-to-one using the actual retraction on stable opens. No sheaf gluing,
nonempty-open assumption or chosen special-fiber frame is required. -/
lemma exists_reduced_gauge : ∃ b : ∀ k, Γ(X,U k)ˣ,
    (∀ k, Units.map (i.app (U k)).hom.toMonoidHom (b k) = 1) ∧
    ∀ k l, d.transition k l = coboundary (StructureUnitsSheaf318.units X).obj U b k l * c.transition k l :=
  ⟨corrected i r U stable a, corrected_reduces i r hr U stable a,
    corrected_equation i r U stable c d rc rd a ha⟩
end SplitReducedGauge318
