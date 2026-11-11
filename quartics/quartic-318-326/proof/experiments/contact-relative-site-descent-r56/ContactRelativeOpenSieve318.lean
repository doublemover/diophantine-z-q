module
public import ContactRelativeFppfSingleton318
public import Mathlib.CategoryTheory.Sites.Canonical
public section
noncomputable section
namespace ContactRelativeOpenSieve318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OriginalRelativeSite318 OriginalRelativeOpenBaseChange318 ContactUniversalRigidifiedClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {Y : Scheme} (b : Y ⟶ FieldBase t)
  (R : Sieve (object b)) {ι : Type} (U : ι → Y.Opens)
  (hc : (⊤ : Y.Opens) ≤ iSup U) (hR : ∀ i, R (openArrow b (U i)))

include hc hR in
/-- A genuine sieve containing a full original open cover satisfies the
sheaf condition, including recovery along every arrow of the sieve. -/
lemma isSheafFor : Presieve.IsSheafFor (presheaf (q t)) R.arrows := by
  intro x hx
  have hm : Presieve.Arrows.Compatible (presheaf (q t)) (fun i => openArrow b (U i))
      (fun i => x (openArrow b (U i)) (hR i)) :=
    fun i j Z gi gj h => hx gi gj (hR i) (hR j) h
  obtain ⟨y,hy,hyuniq⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    (ContactRelativeOpenPresieve318.isSheafFor t b U hc) _ hm
  refine ⟨y,?_,fun y' hy' => hyuniq y' (fun i => hy' _ (hR i))⟩
  intro Z g hg
  obtain ⟨Z,bZ,rfl⟩ := Z.mk_surjective
  apply (ContactRelativeOpenPresieve318.isSheafFor t bZ (fun i => g.left ⁻¹ᵁ U i)
    (inverse_image_cover g.left U hc)).isSeparatedFor.ext
  rintro W a ⟨i⟩
  have hh := hx (restrictedArrow b bZ g.left g.w (U i))
    (openArrow bZ (g.left ⁻¹ᵁ U i)) (hR i) hg (square b bZ g.left g.w (U i))
  rw [← hy i] at hh
  exact (PresheafSingletonSquares318.map_square (presheaf (q t)) g
    (restrictedArrow b bZ g.left g.w (U i)) (openArrow b (U i))
    (openArrow bZ (g.left ⁻¹ᵁ U i)) (square b bZ g.left g.w (U i)) y).symm.trans hh

/-- This is the genuine finest sheaf topology of the original presheaf,
not a topology declared equal to fppf by definition. -/
abbrev topology := Sheaf.finestTopologySingle (presheaf (q t))

include hc hR in
lemma mem_topology : R ∈ topology t (object b) := by
  intro Z g
  obtain ⟨Z,bZ,rfl⟩ := Z.mk_surjective
  apply isSheafFor t bZ (R.pullback g) (fun i => g.left ⁻¹ᵁ U i)
    (inverse_image_cover g.left U hc)
  intro i
  change R (openArrow bZ (g.left ⁻¹ᵁ U i) ≫ g)
  rw [← square b bZ g.left g.w (U i)]
  exact R.downward_closed (hR i) _
end ContactRelativeOpenSieve318
