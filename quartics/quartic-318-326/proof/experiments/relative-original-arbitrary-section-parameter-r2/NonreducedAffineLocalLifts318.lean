module
public import OriginalNonreducedCocycleSplit318
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Abelian
public section
noncomputable section
namespace NonreducedAffineLocalLifts318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme.{0}} [hX : IsAffine X]
abbrev ASheaf := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
variable {F G : ASheaf (X:=X)} (p : F ⟶ G)

structure Data (t : G.obj.obj (op ⊤)) where
  Index : Type
  finiteIndex : Fintype Index
  element : Index → Γ(X,⊤)
  covers : (⨆ i, X.basicOpen (element i)) = ⊤
  localSection : ∀ i, F.obj.obj (op (X.basicOpen (element i)))
  image : ∀ i, p.hom.app _ (localSection i) = G.obj.map (homOfLE le_top).op t

include hX in
/-- Genuine local lifts on a finite original principal cover of ANY affine
scheme. Nilpotents and empty opens are not excluded by an artificial
nonzero-generator requirement. -/
def data [Epi p] (t : G.obj.obj (op ⊤)) : Data p t := by
  classical
  apply Classical.choice
  have hp : TopCat.Presheaf.IsLocallySurjective (X:=X) p.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (X:=X) p).mpr inferInstance
  have localLift (x : X) : ∃ (f : Γ(X,⊤)) (s : F.obj.obj (op (X.basicOpen f))),
      x ∈ X.basicOpen f ∧ p.hom.app _ s = G.obj.map (homOfLE le_top).op t := by
    obtain ⟨V,i,⟨s,hs⟩,hx⟩ := hp.imageSieve_mem t x (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨f,hfV,hxf⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x,hx⟩ trivial
    let r : X.basicOpen f ⟶ V := homOfLE hfV
    refine ⟨f,F.obj.map r.op s,hxf,?_⟩
    have hn : p.hom.app _ (F.obj.map r.op s) = G.obj.map r.op (p.hom.app _ s) :=
      ConcreteCategory.congr_hom (p.hom.naturality r.op) s
    rw [hn,hs,← G.obj.map_comp_apply]
    rfl
  choose f s hx hs using localLift
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨⟨I,inferInstance,fun x => f x,?_,fun x => s x,fun x => hs x⟩⟩
  apply top_unique
  intro x hx'
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ x))
  exact (le_iSup (fun y : I => X.basicOpen (f y)) ⟨y,hy⟩) hxy
end NonreducedAffineLocalLifts318
