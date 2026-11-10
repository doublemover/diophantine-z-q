module
public import ActualPrincipalCocycle318
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Abelian

public section
noncomputable section
namespace AffinePrincipalLocalLifts318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : CommRingCat.{0}}
abbrev ASheaf := CategoryTheory.Sheaf (Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{0}
abbrev toTop (f : R) : PrimeSpectrum.basicOpen f ⟶ (⊤ : Opens (PrimeSpectrum R)) :=
  homOfLE le_top
variable {F G : ASheaf (R:=R)} (p : F ⟶ G)

structure Data (t : G.obj.obj (op ⊤)) where
  Index : Type
  finiteIndex : Fintype Index
  element : Index → R
  nonzero : ∀ i, element i ≠ 0
  covers : (⨆ i, PrimeSpectrum.basicOpen (element i)) = ⊤
  localSection : ∀ i, F.obj.obj (op (PrimeSpectrum.basicOpen (element i)))
  image : ∀ i, p.hom.app _ (localSection i) = G.obj.map (toTop (element i)).op t

/-- Any section under an actual epimorphism of additive sheaves lifts on a finite
principal cover. All chosen principal elements are nonzero because their opens contain points. -/
@[expose] def data [Epi p] (t : G.obj.obj (op ⊤)) : Data p t := by
  classical
  apply Classical.choice
  have hp : TopCat.Presheaf.IsLocallySurjective (X:=PrimeSpectrum.Top R) p.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (X:=PrimeSpectrum.Top R) p).mpr inferInstance
  have localLift (x : PrimeSpectrum R) : ∃ (f : R) (s : F.obj.obj (op (PrimeSpectrum.basicOpen f))),
      x ∈ PrimeSpectrum.basicOpen f ∧ p.hom.app _ s =
        G.obj.map (toTop f).op t := by
    obtain ⟨V,i,⟨s,hs⟩,hx⟩ := hp.imageSieve_mem t x (show x ∈ (⊤ : Opens (PrimeSpectrum R)) from trivial)
    obtain ⟨U,⟨_,⟨f,rfl⟩,rfl⟩,hxf,hfV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx V.2
    let r : PrimeSpectrum.basicOpen f ⟶ V := homOfLE hfV
    refine ⟨f,F.obj.map r.op s,hxf,?_⟩
    have hn : p.hom.app _ (F.obj.map r.op s) = G.obj.map r.op (p.hom.app _ s) :=
      ConcreteCategory.congr_hom (p.hom.naturality r.op) s
    rw [hn,hs,← G.obj.map_comp_apply]
    rfl
  choose f s hx hs using localLift
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum R => (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (f x)).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨⟨I,inferInstance,fun x => f x,fun x => ?_,?_,fun x => s x,fun x => hs x⟩⟩
  · intro h
    simpa [h] using hx x
  · apply top_unique
    intro x hx'
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ x))
    exact (le_iSup (fun y : I => PrimeSpectrum.basicOpen (f y)) ⟨y,hy⟩) hxy

end AffinePrincipalLocalLifts318
