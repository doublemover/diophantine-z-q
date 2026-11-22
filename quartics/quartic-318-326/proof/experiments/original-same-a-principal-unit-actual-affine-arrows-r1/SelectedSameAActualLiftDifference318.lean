module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
An actual pair of local cotangent lifts differs by one unique
section of the *actual* first term. This is detected by the kernel
of the original row on the actual open, not by postulating a torsor.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAActualLiftDifference318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]

abbrev Sh := Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}

variable (S : ShortComplex (Sh X))

private abbrev sections (U : Opens X) : Sh X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

/-- Sheaf evaluation preserves the actual kernel, even though it need
not preserve the epi onto the whole section group. -/
def original_left_kernel_at_open (hS : S.ShortExact) (U : Opens X) :
    IsLimit (KernelFork.ofι (S.f.hom.app (op U))
      (show S.f.hom.app (op U) ≫ S.g.hom.app (op U) = 0 from by
        have h := congrArg (fun m : S.X₁ ⟶ S.X₃ => m.hom.app (op U)) S.zero
        exact h)) := by
  let F := sections X U
  letI : F.PreservesZeroMorphisms := by
    dsimp only [F, sections]
    infer_instance
  letI : PreservesLimit (parallelPair S.g (0 : S.X₂ ⟶ S.X₃)) F := by
    dsimp only [F, sections]
    infer_instance
  exact KernelFork.mapIsLimit (KernelFork.ofι S.f S.zero) hS.fIsKernel F

private theorem local_inclusion_isMono (hS : S.ShortExact) (U : Opens X) :
    Mono (S.f.hom.app (op U)) :=
  mono_of_isLimit_fork (original_left_kernel_at_open X S hS U)

theorem local_inclusion_injective (hS : S.ShortExact) (U : Opens X) :
    Function.Injective (S.f.hom.app (op U)) := by
  letI : Mono (S.f.hom.app (op U)) := local_inclusion_isMono X S hS U
  exact (AddCommGrpCat.mono_iff_injective (S.f.hom.app (op U))).mp inferInstance

/-- A difference in the actual kernel has a real section in the given
first term, with the actual first-arrow evaluation as its beta. -/
theorem local_kernel_has_value (hS : S.ShortExact) (U : Opens X)
    (b : S.X₂.obj.obj (op U)) (hb : S.g.hom.app (op U) b = 0) :
    ∃ d : S.X₁.obj.obj (op U), S.f.hom.app (op U) d = b := by
  let q := S.g.hom.app (op U)
  let k := AddCommGrpCat.kernelIsoKer q
  let e := IsLimit.conePointUniqueUpToIso (original_left_kernel_at_open X S hS U)
    (kernelIsKernel q)
  have he : e.hom ≫ kernel.ι q = S.f.hom.app (op U) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  let b' : ↥q.hom.ker := ⟨b, hb⟩
  let d := e.inv (k.inv b')
  refine ⟨d, ?_⟩
  have hv := congrArg (fun m : S.X₁.obj.obj (op U) ⟶ S.X₂.obj.obj (op U) => m d) he
  have hk := congrArg (fun m : AddCommGrpCat.of ↥q.hom.ker ⟶ S.X₂.obj.obj (op U) => m b')
    (AddCommGrpCat.kernelIsoKer_inv_comp_ι q)
  change kernel.ι q (e.hom (e.inv (k.inv b'))) = S.f.hom.app (op U) d at hv
  change kernel.ι q (k.inv b') = b at hk
  have hh : e.hom (e.inv (k.inv b')) = k.inv b' :=
    Iso.inv_hom_id_apply (C := AddCommGrpCat) e _
  exact hv.symm.trans ((congrArg (kernel.ι q) hh).trans hk)

/-- The sign is right lift minus left lift. The filtration \(d\epsilon\)
is never quotiented out; here the first map is still the literal one. -/
theorem difference_unique (hS : S.ShortExact) (U : Opens X)
    (l r : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) l = S.g.hom.app (op U) r) :
    ∃! d : S.X₁.obj.obj (op U), S.f.hom.app (op U) d = r - l := by
  have hz : S.g.hom.app (op U) (r - l) = 0 := by
    exact ((S.g.hom.app (op U)).hom.map_sub r l).trans (sub_eq_zero.mpr h.symm)
  obtain ⟨d, hd⟩ := local_kernel_has_value X S hS U (r - l) hz
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact local_inclusion_injective X S hS U (hd'.trans hd.symm)

end SelectedSameAActualLiftDifference318
