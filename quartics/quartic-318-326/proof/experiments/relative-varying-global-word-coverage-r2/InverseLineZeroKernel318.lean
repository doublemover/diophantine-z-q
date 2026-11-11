module
public import InverseLineSectionContraction318
public import ActualClosedIdealModule318
public import ModuleLocalInverse318
public section
noncomputable section
namespace InverseLineZeroKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ModuleLocalGluing318 InverseLineSectionContraction318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X) (L : Line X) (s : Γ(L.object,⊤))
local notation "I" => FramedLineInverse318.inverse L
local notation "f" => InverseLineSectionContraction318.hom L s
local notation "K" => ActualClosedIdealModule318.object p
local notation "ι" => ActualClosedIdealModule318.inclusion p
local notation "g" => ActualClosedIdealModule318.structure p

/-- The precise original-zero comparison still required by this generic
bridge. It concerns literal kernels on EVERY framed subopen, not reduced
supports, stalk-point bijectivity, or an abstract line of the same degree. -/
def LocalZeroEquations : Prop := ∀ i V (h : V≤L.opens i),
  RingHom.ker (p.app V).hom =
    Ideal.span {coordinate L i V h (res L.object (show V≤⊤ from le_top) s)}

variable (hz : LocalZeroEquations p L s)

lemma local_killed (i : L.Index) (V : X.Opens) (h : V≤L.opens i)
    (a : Γ(I.object,V)) : g.app V (f.app V a)=0 := by
  rw [ActualClosedIdealModule318.structure_app]
  have hm : f.app V a ∈ LinearMap.range (f.val.app (op V)).hom := ⟨a,rfl⟩
  rw [range_on_subopen L s i V h,← hz i V h] at hm
  exact hm

/-- The original globally glued contraction actually dies in p_*O_Z.
The proof uses separatedness and the same original full cover. -/
lemma killed : f ≫ g=0 := by
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  apply ext_value L.cover V
  intro i
  change res (ActualClosedIdealModule318.target p) (show V⊓L.opens i≤V from inf_le_left)
    (g.app V (f.app V a))=res (ActualClosedIdealModule318.target p) inf_le_left 0
  rw [ModuleLocalInverse318.natural g,ModuleLocalInverse318.natural f]
  rw [local_killed p L s hz i _ inf_le_right]
  exact (map_zero _).symm

/-- Canonical factor through the genuine module-sheaf kernel, with no
conversion of IdealSheafData into a module. -/
@[expose] def factor : I.object ⟶ K := kernel.lift g f (killed p L s hz)

@[reassoc] lemma factor_inclusion : factor p L s hz ≫ ι=f := kernel.lift_ι _ _ _

lemma factor_value (V : X.Opens) (a : Γ(I.object,V)) :
    ι.app V ((factor p L s hz).app V a)=f.app V a :=
  congrArg (fun k => k.app V a) (factor_inclusion p L s hz)

lemma inclusion_injective (V : X.Opens) : Function.Injective (ι.app V) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op V)
  haveI : Mono (E.map ι) := inferInstance
  exact (ModuleCat.mono_iff_injective (E.map ι)).mp inferInstance

lemma factor_surjective (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :
    Function.Surjective ((factor p L s hz).app V) := by
  intro a
  have hzero : g.app V (ι.app V a)=0 :=
    congrArg (fun k => k.app V a) (ActualClosedIdealModule318.inclusion_structure p)
  rw [ActualClosedIdealModule318.structure_app] at hzero
  have hm : ι.app V a ∈ LinearMap.range (f.val.app (op V)).hom := by
    rw [range_on_subopen L s i V h,← hz i V h]
    exact hzero
  obtain ⟨b,hb⟩ := hm
  refine ⟨b,?_⟩
  apply inclusion_injective p V
  rw [factor_value]
  exact hb

/-- This is the actual regular-equation hypothesis, not regularity of
an arbitrary specialization deduced from universal total-space regularity. -/
def LocalRegular : Prop := ∀ i V (h : V≤L.opens i) (a : Γ(X,V)),
  a * coordinate L i V h (res L.object (show V≤⊤ from le_top) s)=0 → a=0

variable (hr : LocalRegular L s)

lemma factor_bijective (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :
    Function.Bijective ((factor p L s hz).app V) := by
  refine ⟨?_,factor_surjective p L s hz i V h⟩
  intro a b hab
  apply injective_on_subopen L s i V h (hr i V h)
  have he := congrArg (fun t => ι.app V t) hab
  simpa only [factor_value] using he

/-- The GLOBAL inverse-line identification, when the exact original local
zero equations and actual regular coordinates are supplied. Its forward
map is the canonical kernel factor, and its composite with the original
kernel inclusion is exactly the previously constructed contraction. -/
@[expose] def iso : I.object ≅ K :=
  ModuleLocalInverse318.iso (factor p L s hz) L.opens L.cover
    (factor_bijective p L s hz hr)

@[reassoc] lemma iso_hom_inclusion : (iso p L s hz hr).hom ≫ ι=f :=
  factor_inclusion p L s hz
end InverseLineZeroKernel318
