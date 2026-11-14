module
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public section
noncomputable section
namespace FiniteClosedSupportSheaf318
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat
universe u
attribute [local instance] Classical.propDecidable
/-- If only one factor can be nonzero, its actual product projection
is an isomorphism; the inverse is the canonical zero-filled inclusion. -/
lemma projection_iso {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} (A : I → C) [HasProduct A] (i : I)
    (h : ∀ j, j ≠ i → IsZero (A j)) : IsIso (Pi.π A i) := by
  refine ⟨⟨Pi.ι A i,?_,Pi.ι_π_eq_id A i⟩⟩
  apply Pi.hom_ext
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · exact (h j hj).eq_of_tgt _ _
lemma product_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} (A : I → C) [HasProduct A] (h : ∀ i, IsZero (A i)) :
    IsZero (∏ᶜ A) := by
  rw [IsZero.iff_id_eq_zero]
  apply Pi.hom_ext
  intro i
  exact (h i).eq_of_tgt _ _
variable {X : TopCat.{u}} (F : Sheaf Ab X) {I : Type u} [Finite I] (p : I → X)
@[expose] def pieces : I → Sheaf Ab X :=
  fun i => skyscraperSheaf (p i) (F.obj.stalk (p i))
@[expose] def toPieces : F ⟶ ∏ᶜ pieces F p :=
  Pi.lift (fun i => (stalkSkyscraperSheafAdjunction (p i)).unit.app F)
lemma unit_stalk_iso (x : X) :
    IsIso ((Sheaf.forget Ab X ⋙ Presheaf.stalkFunctor Ab x).map
      ((stalkSkyscraperSheafAdjunction x).unit.app F)) := by
  let adj := stalkSkyscraperSheafAdjunction (C := Ab) x
  haveI : IsIso (adj.counit.app (F.obj.stalk x)) := by
    change IsIso (skyscraperPresheafStalkOfSpecializes x (F.obj.stalk x) specializes_rfl).hom
    infer_instance
  haveI : IsIso ((Sheaf.forget Ab X ⋙ Presheaf.stalkFunctor Ab x).map
      (adj.unit.app F) ≫ adj.counit.app (F.obj.stalk x)) := by
    rw [adj.left_triangle_components]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (F.obj.stalk x))
lemma piece_stalk_zero (hp : ∀ i, IsClosed ({p i} : Set X)) (x : X) (i : I)
    (hi : p i ≠ x) :
    IsZero ((Sheaf.forget Ab X ⋙ Presheaf.stalkFunctor Ab x).obj (pieces F p i)) := by
  have hn : ¬p i ⤳ x := by
    rw [specializes_iff_mem_closure,(hp i).closure_eq,Set.mem_singleton_iff]
    exact Ne.symm hi
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal (p i) (F.obj.stalk (p i)) hn).isZero
/-- A sheaf of abelian groups with support in a finite set of distinct
closed points is the product of its ACTUAL skyscraper stalk sheaves.
The morphism is the genuine adjunction unit at each support point. -/
theorem toPieces_isIso (hinj : Function.Injective p)
    (hp : ∀ i, IsClosed ({p i} : Set X))
    (hz : ∀ x, x ∉ Set.range p → IsZero (F.obj.stalk x)) : IsIso (toPieces F p) := by
  rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro x
  let G := Sheaf.forget Ab X ⋙ Presheaf.stalkFunctor Ab x
  change IsIso (G.map (toPieces F p))
  haveI : IsIso (piComparison G (pieces F p)) := inferInstance
  by_cases hx : x ∈ Set.range p
  · obtain ⟨i,rfl⟩ := hx
    haveI : IsIso (Pi.π (fun j => G.obj (pieces F p j)) i) :=
      projection_iso _ i (fun j hj => piece_stalk_zero F p hp (p i) j
        (fun h => hj (hinj h)))
    haveI : IsIso (G.map (Pi.π (pieces F p) i)) := by
      rw [←piComparison_comp_π]
      infer_instance
    have he : G.map (toPieces F p) ≫ G.map (Pi.π (pieces F p) i) =
        G.map ((stalkSkyscraperSheafAdjunction (p i)).unit.app F) := by
      rw [←Functor.map_comp]
      congr 1
      exact Pi.lift_π _ i
    haveI : IsIso (G.map (toPieces F p) ≫ G.map (Pi.π (pieces F p) i)) := by
      rw [he]
      exact unit_stalk_iso F (p i)
    exact IsIso.of_isIso_comp_right _ (G.map (Pi.π (pieces F p) i))
  · have ht : IsZero (∏ᶜ fun i => G.obj (pieces F p i)) :=
      product_zero _ (fun i => piece_stalk_zero F p hp x i (fun h => hx ⟨i,h⟩))
    have ht' : IsZero (G.obj (∏ᶜ pieces F p)) := ht.of_iso (asIso (piComparison G (pieces F p)))
    exact isIso_of_source_target_iso_zero _ (hz x hx).isoZero ht'.isoZero
end FiniteClosedSupportSheaf318
