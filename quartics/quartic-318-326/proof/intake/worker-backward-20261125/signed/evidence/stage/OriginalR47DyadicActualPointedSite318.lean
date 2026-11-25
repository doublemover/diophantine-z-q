module
public import OriginalR47DyadicFixedReesCentre318
public import OriginalR47ActualPointedRound318
public section
noncomputable section

namespace OriginalR47DyadicActualPointedSite318

open AlgebraicGeometry CategoryTheory
open OriginalThickCentralReesChart318 (O I x y)
open OriginalR47DyadicFixedReesCentre318 (contracted retained_origin)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {D A B : Type u} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
  [CommRing A] [CommRing B]
variable {X U : Scheme.{u}} (e : U ⟶ X)
variable (q : D) (d : ℕ)
variable (l : U ⟶ Spec (CommRingCat.of (O q d)))
variable (v : Spec (CommRingCat.of B) ⟶ U) (z : PrimeSpectrum B) (u₀ : U)

abbrev readNode : O q d →+* B :=
  (Spec.preimage (v ≫ l)).hom

/-- Use the actual split-arrow given by the marked old window. The
morphism from the wild normalized proof chart need not be étale; the
paired arrows e/l of the *old* pointed window must be. Therefore this
consumer never substitutes the wild covering map for an étale map. -/
theorem into_existing_round (hq : Irreducible q) (hv : v z = u₀)
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (p : Ideal A) [p.IsMaximal] (hj : e u₀ = j ⟨p,inferInstance⟩)
    [Flat e] [FormallyUnramified e] [LocallyOfFiniteType e]
    [Flat l] [FormallyUnramified l] [LocallyOfFiniteType l]
    (a b X₁ Y₁ : B) (n i j₁ : ℕ) (hi : i ≠ 0) (hj₁ : j₁ ≠ 0)
    (ha : a ∉ z.asIdeal) (hb : b ∉ z.asIdeal)
    (hx : readNode q d l v (x q d) = a * X₁^i)
    (hy : readNode q d l v (y q d) = b * Y₁^j₁)
    (haxis : Even n ↔ X₁ ∈ z.asIdeal ∧ Y₁ ∈ z.asIdeal) (hn : Even n) :
    Nonempty (OriginalR47ActualPointedRound318.Actual q d p e l j u₀) := by
  have h₀ : contracted q d (readNode q d l v) z = l u₀ := by
    change Spec.map (Spec.preimage (v ≫ l)) z = l u₀
    rw [Spec.map_preimage,Scheme.Hom.comp_apply,hv]
  have h := (retained_origin q hq d (readNode q d l v) z a b X₁ Y₁ n i j₁
    hi hj₁ ha hb hx hy haxis).mp hn
  rw [h₀] at h
  exact OriginalR47ActualPointedRound318.of_dvr_site q d p e l j u₀ hq hj h

end OriginalR47DyadicActualPointedSite318

#print axioms OriginalR47DyadicActualPointedSite318.into_existing_round
