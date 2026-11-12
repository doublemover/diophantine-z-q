module
public import ContactHilbertIdealCoefficient318
public section
noncomputable section
namespace RegularClosedKernelTransport318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z W X : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ X)
  [IsClosedImmersion p] [IsClosedImmersion q] (e : Z ≅ W) (he : e.hom ≫ q=p)
include he in
lemma kernel : p.ker=q.ker := by
  have h := Scheme.Hom.ker_comp_of_isIso e.hom q
  have h' := congrArg (fun f : Z ⟶ X => f.ker) he
  exact h'.symm.trans h
include he in
lemma regular_iff : OriginalRegularClosedCharts318.Property p ↔ OriginalRegularClosedCharts318.Property q := by
  constructor
  · exact RegularClosedIso318.transport p q e he
  · intro h
    apply RegularClosedIso318.transport q p e.symm ?_ h
    rw [← he,← Category.assoc,Iso.symm_hom,Iso.inv_hom_id,Category.id_comp]
variable (hp : OriginalRegularClosedCharts318.Property p) (hq : OriginalRegularClosedCharts318.Property q)
/-- Actual full ideal-kernel transport, preserving the literal structure
sheaf inclusion, across a source-preserving family isomorphism. -/
@[expose] def kernelIso : (ActualCartierIdealLine318.line p hp).object ≅
    (ActualCartierIdealLine318.line q hq).object :=
  CartierKernelEquality318.iso p q hp hq (kernel p q e he)
@[reassoc] lemma inclusion : (kernelIso p q e he hp hq).hom ≫ ActualClosedIdealModule318.inclusion q=
    ActualClosedIdealModule318.inclusion p := CartierKernelEquality318.iso_inclusion _ _ _ _ _
lemma dual_class : classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line p hp))=
    classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line q hq)) := by
  rw [LineSheafClassGroup318.classOf_inverse,LineSheafClassGroup318.classOf_inverse]
  exact congrArg (fun x => x⁻¹) (classOf_eq (kernelIso p q e he hp hq))
end RegularClosedKernelTransport318
