module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

/-!
Actual sections of the injective target extend over each true open
inclusion. The mono is constructed from the free representable sheaf;
no flasqueness or extension-family proof is an input.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAInjectiveOpenExtension318

universe u

variable (X : TopCat.{u})
variable [HasSheafify (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}]

abbrev site := _root_.Opens.grothendieckTopology X
abbrev Sh := Sheaf (site X) AddCommGrpCat.{u}

abbrev freeObj (U : Opens X) := yoneda.obj U ⋙ AddCommGrpCat.free

abbrev freeMap {U V : Opens X} (f : U ⟶ V) : freeObj X U ⟶ freeObj X V :=
  Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free

abbrev Gen (U : Opens X) :=
  (presheafToSheaf (site X) AddCommGrpCat.{u}).obj (freeObj X U)

abbrev genMap {U V : Opens X} (f : U ⟶ V) : Gen X U ⟶ Gen X V :=
  (presheafToSheaf (site X) AddCommGrpCat.{u}).map (freeMap X f)

/-- The actual sheafified free generator map is mono, not an
assumed boundary property of the open inclusion. -/
theorem genMap_mono {U V : Opens X} (f : U ⟶ V) : Mono (genMap X f) := by
  letI : Mono (yoneda.map f) := (NatTrans.mono_iff_mono_app _).2 (fun W => by
    apply (CategoryTheory.mono_iff_injective _).2
    intro a b hab
    change (a : W.unop ⟶ U) = b
    exact Subsingleton.elim _ _)
  letI : Mono (freeMap X f) :=
    inferInstanceAs (Mono (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free))
  letI : (plusPlusSheaf (site X) AddCommGrpCat.{u}).PreservesMonomorphisms := inferInstance
  letI : (presheafToSheaf (site X) AddCommGrpCat.{u}).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (plusPlusSheafIsoPresheafToSheaf _ _)
  exact (presheafToSheaf (site X) AddCommGrpCat.{u}).map_mono (freeMap X f)

variable (F : Sh X)

private def rawLift (U : Opens X) (s : F.obj.obj (op U)) : freeObj X U ⟶ F.obj where
  app W := AddCommGrpCat.ofHom (FreeAbelianGroup.lift
    (fun g : W.unop ⟶ U => F.obj.map g.op s))
  naturality V W i := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro g
    change FreeAbelianGroup.lift (fun g : W.unop ⟶ U => F.obj.map g.op s)
      (FreeAbelianGroup.map (fun g : V.unop ⟶ U => i.unop ≫ g) (FreeAbelianGroup.of g)) =
      F.obj.map i (FreeAbelianGroup.lift (fun g : V.unop ⟶ U => F.obj.map g.op s)
        (FreeAbelianGroup.of g))
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of]
    rw [← F.obj.map_comp_apply]
    rfl

private def rawRead (U : Opens X) (g : freeObj X U ⟶ F.obj) :
    F.obj.obj (op U) := g.app (op U) (FreeAbelianGroup.of (𝟙 U))

private def read (U : Opens X) (g : Gen X U ⟶ F) : F.obj.obj (op U) :=
  rawRead X F U ((sheafificationAdjunction (site X) AddCommGrpCat.{u}).homEquiv
    (freeObj X U) F g)

private def fromSection (U : Opens X) (s : F.obj.obj (op U)) : Gen X U ⟶ F :=
  ((sheafificationAdjunction (site X) AddCommGrpCat.{u}).homEquiv
    (freeObj X U) F).symm (rawLift X F U s)

private theorem read_fromSection (U : Opens X) (s : F.obj.obj (op U)) :
    read X F U (fromSection X F U s) = s := by
  unfold read fromSection
  rw [Equiv.apply_symm_apply]
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of (𝟙 U)) = s
  rw [FreeAbelianGroup.lift_apply_of]
  change F.obj.map (𝟙 (op U)) s = s
  rw [F.obj.map_id] <;> rfl

private theorem raw_restrict {U V : Opens X} (f : U ⟶ V)
    (g : freeObj X V ⟶ F.obj) :
    rawRead X F U (freeMap X f ≫ g) = F.obj.map f.op (rawRead X F V g) := by
  have h := ConcreteCategory.congr_hom (g.naturality f.op) (FreeAbelianGroup.of (𝟙 V))
  simpa [rawRead, freeMap, freeObj] using h

private theorem read_restrict {U V : Opens X} (f : U ⟶ V) (g : Gen X V ⟶ F) :
    read X F U (genMap X f ≫ g) = F.obj.map f.op (read X F V g) := by
  exact (congrArg (rawRead X F U)
    ((sheafificationAdjunction (site X) AddCommGrpCat.{u}).homEquiv_naturality_left
      (freeMap X f) g)).trans (raw_restrict X F f _)

/-- Actual open-extension theorem for the same concrete Zariski
additive sheaf site and any actual injective object on it. -/
theorem restriction_surjective [Injective F] {U V : Opens X} (f : U ⟶ V) :
    Function.Surjective (F.obj.map f.op) := by
  intro s
  letI := genMap_mono X f
  let a := fromSection X F U s
  let b := Injective.factorThru a (genMap X f)
  refine ⟨read X F V b, ?_⟩
  have h : genMap X f ≫ b = a := Injective.comp_factorThru a (genMap X f)
  exact (read_restrict X F f b).symm.trans
    ((congrArg (read X F U) h).trans (read_fromSection X F U s))

end SelectedSameAInjectiveOpenExtension318
