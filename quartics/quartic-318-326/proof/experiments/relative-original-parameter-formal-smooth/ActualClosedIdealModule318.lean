module
public import ModuleGlobalSections318
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public section
noncomputable section
namespace ActualClosedIdealModule318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X)

abbrev source : X.Modules := SheafOfModules.unit X.ringCatSheaf
abbrev target : X.Modules := (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Z.ringCatSheaf)

/-- The actual O_X-linear structure morphism into p_*O_Z, formed from
the literal section1 of the pushed structure sheaf. -/
@[expose] def structure : source (X:=X) ⟶ target p :=
  ModuleGlobalSections318.ofTop (target p) (1 : Γ(Z,p ⁻¹ᵁ ⊤))

lemma structure_app (U : X.Opens) (a : Γ(X,U)) :
    (structure p).app U a=(p.app U) a := by
  rw [structure,ModuleGlobalSections318.ofTop_apply]
  change (p.app U) a * (Z.presheaf.map _ (1 : Γ(Z,p ⁻¹ᵁ ⊤)))=(p.app U) a
  rw [map_one,mul_one]

/-- An ACTUAL sheaf of O_X-modules, not merely IdealSheafData. This is
the kernel of the original structure morphism before choosing any charts. -/
@[expose] def object : X.Modules := kernel (structure p)
@[expose] def inclusion : object p ⟶ source (X:=X) := kernel.ι (structure p)
instance inclusion_mono : Mono (inclusion p) := inferInstance

@[reassoc] lemma inclusion_structure : inclusion p ≫ structure p=0 := kernel.condition _

variable (U : X.Opens)
local notation "E" => SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- Canonical section comparison: sheaf evaluation preserves the actual
kernel, and the ModuleCat kernel is the actual linear-map kernel. -/
@[expose] def sectionsIso : E.obj (object p) ≅ ModuleCat.of Γ(X,U)
    (LinearMap.ker (E.map (structure p)).hom) :=
  PreservesKernel.iso E (structure p) ≪≫ ModuleCat.kernelIsoKer (E.map (structure p))

/-- The comparison retains the original inclusion into O_X, not just
an isomorphism of abstract kernel modules. -/
@[reassoc] lemma sectionsIso_inv_inclusion :
    (sectionsIso p U).inv ≫ E.map (inclusion p)=
      ModuleCat.ofHom (LinearMap.ker (E.map (structure p)).hom).subtype := by
  simp only [sectionsIso,Iso.trans_inv,Category.assoc,PreservesKernel.iso_inv_ι,
    inclusion,ModuleCat.kernelIsoKer_inv_kernel_ι]

/-- Its actual section kernel is exactly the ring-theoretic ideal of
functions killed by p.app on the SAME open. No radical or support test. -/
lemma section_kernel : LinearMap.ker (E.map (structure p)).hom = RingHom.ker (p.app U).hom := by
  ext a
  change (structure p).app U a=0 ↔ (p.app U) a=0
  rw [structure_app]
/-- For a quasi-compact map, this actual module sheaf realizes the
EXISTING ideal-sheaf DATA on every affine open. Quasi-compactness is not
silently omitted from the data-to-kernel comparison. -/
lemma section_kernel_idealData [QuasiCompact p] (V : X.affineOpens) :
    LinearMap.ker ((SheafOfModules.evaluation X.ringCatSheaf (op V.1)).map (structure p)).hom =
      p.ker.ideal V :=
  (section_kernel p V.1).trans (p.ker_apply V).symm
end ActualClosedIdealModule318
