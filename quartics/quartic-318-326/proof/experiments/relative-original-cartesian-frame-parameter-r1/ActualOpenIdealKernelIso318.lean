module
public import ActualOpenIdealRange318
public import InvertibleIdealUniqueness318
public section
noncomputable section
namespace ActualOpenIdealKernelIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {Z X W Y : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (q : W ⟶ Y) (k : W ⟶ Z) (j : Y ⟶ X) [IsOpenImmersion j]
  (hs : IsPullback q k j p)
local instance : QuasiCompact q := MorphismProperty.of_isPullback hs.flip inferInstance
local notation "f" => ActualOpenIdealInclusion318.hom p j

lemma exact_on_basis (V : Y.affineOpens) :
    LinearMap.range (f.val.app (op V.1)).hom=
      LinearMap.ker ((ActualClosedIdealModule318.structure q).val.app (op V.1)).hom :=
  (ActualOpenIdealRange318.range_eq p q k j hs V).trans
    (ActualClosedIdealModule318.section_kernel_idealData q V).symm

/-- The actual original ideal kernel sheaf restricts to the actual kernel
of the original open Cartesian base change. This retains the full scheme
ideals and exact inclusion, not just abstract line classes or point sets. -/
@[expose] def iso : (ActualClosedIdealModule318.object p).restrict j ≅
    ActualClosedIdealModule318.object q :=
  ModuleBasisKernel318.iso f (ActualClosedIdealModule318.structure q)
    (fun V : Y.affineOpens => V.1) InvertibleIdealUniqueness318.basis
    (exact_on_basis p q k j hs) (fun V => ActualOpenIdealInclusion318.injective p j V.1)

@[reassoc] lemma inclusion : (iso p q k j hs).hom ≫ ActualClosedIdealModule318.inclusion q=f :=
  ModuleBasisKernel318.iso_hom_inclusion f (ActualClosedIdealModule318.structure q)
    (fun V : Y.affineOpens => V.1) InvertibleIdealUniqueness318.basis
    (exact_on_basis p q k j hs) (fun V => ActualOpenIdealInclusion318.injective p j V.1)
end ActualOpenIdealKernelIso318
