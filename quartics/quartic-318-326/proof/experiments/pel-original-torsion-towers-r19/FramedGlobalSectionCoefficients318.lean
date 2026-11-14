module
public import LineFrameCocycle318
public import ModuleGlobalSections318
public section
noncomputable section
namespace FramedGlobalSectionCoefficients318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (e : ∀ i, SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (s : Γ(M,⊤))

@[expose] def coefficient (i : ι) : Γ(X,U i) :=
  (OpenLineFrameCoordinates318.frame M (U i) (e i) (U i) le_rfl).symm
    (M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op s)

/-- Every algebraic global section has its exact coefficient in the
actual frame on EVERY smaller open, retaining original restrictions. -/
theorem framed_value (i : ι) (V : X.Opens) (hV : V ≤ U i) :
    OpenLineFrameCoordinates318.frame M (U i) (e i) V hV
      (X.presheaf.map (homOfLE hV).op (coefficient M U e s i))=
      M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s := by
  rw [←OpenLineFrameCoordinates318.natural M (U i) (e i) le_rfl hV,
    coefficient,LinearEquiv.apply_symm_apply]
  have h := congrArg (fun f => f s)
    (M.presheaf.map_comp (homOfLE (show U i ≤ ⊤ from le_top)).op (homOfLE hV).op)
  exact h.symm

/-- Arbitrary genuine global sections satisfy the extracted frame
cocycle on the WHOLE overlap, without a point-evaluation assumption. -/
theorem transition (i j : ι) :
    X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
      (coefficient M U e s i)=
    ((LineFrameCocycle318.cocycle M U e).transition i j).val *
      X.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
        (coefficient M U e s j) := by
  apply (OpenLineFrameCoordinates318.frame M (U i) (e i) (U i ⊓ U j) inf_le_left).injective
  rw [LineFrameTransitions318.relation,framed_value,framed_value]
end FramedGlobalSectionCoefficients318
