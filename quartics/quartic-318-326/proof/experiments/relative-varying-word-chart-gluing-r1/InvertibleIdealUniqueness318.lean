module
public import ActualClosedIdealRange318
public import ModuleBasisKernel318
public import LineSheafClass318
public section
noncomputable section
namespace InvertibleIdealUniqueness318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (L : LineSheafClass318.Line X) (f : L.object ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono f]
  (he : ∀ V : X.affineOpens,LinearMap.range (f.val.app (op V.1)).hom=p.ker.ideal V)

lemma basis : Opens.IsBasis (Set.range (fun V : X.affineOpens => V.1)) := by
  convert! X.isBasis_affineOpens using 1
  exact Subtype.range_coe_subtype

lemma exact_on_basis (V : X.affineOpens) :
    LinearMap.range (f.val.app (op V.1)).hom=
      LinearMap.ker ((ActualClosedIdealModule318.structure p).val.app (op V.1)).hom :=
  (he V).trans (ActualClosedIdealModule318.section_kernel_idealData p V).symm

lemma injective_on_basis (V : X.affineOpens) : Function.Injective (f.app V.1) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op V.1)
  haveI : Mono (E.map f) := inferInstance
  exact (ModuleCat.mono_iff_injective (E.map f)).mp inferInstance

/-- Every genuine invertible ideal presentation of the SAME original
closed subscheme identifies with its actual global kernel. Equality of
literal ideals on the full affine basis is sufficient; no support-only
or arbitrarily selected line-class comparison enters. -/
@[expose] def iso : L.object ≅ ActualClosedIdealModule318.object p :=
  ModuleBasisKernel318.iso f (ActualClosedIdealModule318.structure p)
    (fun V : X.affineOpens => V.1) basis
    (exact_on_basis p L f he) (injective_on_basis L f)

@[reassoc] lemma inclusion : (iso p L f he).hom ≫ ActualClosedIdealModule318.inclusion p=f :=
  ModuleBasisKernel318.iso_hom_inclusion f (ActualClosedIdealModule318.structure p)
    (fun V : X.affineOpens => V.1) basis
    (exact_on_basis p L f he) (injective_on_basis L f)

lemma unique (a : L.object ⟶ ActualClosedIdealModule318.object p)
    (ha : a ≫ ActualClosedIdealModule318.inclusion p=f) : a=(iso p L f he).hom := by
  apply (cancel_mono (ActualClosedIdealModule318.inclusion p)).mp
  exact ha.trans (inclusion p L f he).symm
end InvertibleIdealUniqueness318
