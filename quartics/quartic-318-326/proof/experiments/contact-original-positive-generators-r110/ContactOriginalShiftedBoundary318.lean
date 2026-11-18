module
public import ContactOriginalLaurentBoundary318
public import LaurentPositiveTwistVanishing318
public section
noncomputable section
namespace ContactOriginalShiftedBoundary318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open LaurentVectorFiltration318 ContactOriginalLaurentCoordinates318
open ContactOriginalRestrictionCoordinates318 ContactOriginalLineBothCharts318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c)) (d : ℤ)

/-- The shifted negative image consists of the ORIGINAL infinity-chart
restrictions multiplied by the actual monomial. Rank transport is inherited
from the proved old common-module comparison. -/
lemma negative_image (v : V ℚ (finiteRank c L)) :
    v ∈ negative.map (LaurentTransitionBounds318.underlying
      (LaurentPositiveTwistVanishing318.transition (transition c L) d)) ↔
    ∃ b : infinitySections c L,
      (LaurentPolynomial.T d : A) • coordinates c L (infinityRestriction c L b) = v := by
  have him (x : V ℚ (finiteRank c L)) :
      (∃ b : infinitySections c L, coordinates c L (infinityRestriction c L b) = x) ↔
        x ∈ negative.map (LaurentTransitionBounds318.underlying (transition c L)) := by
    rw [ContactOriginalLaurentBoundary318.negative_image]
    exact Set.ext_iff.mp (infinity_image c L) x
  constructor
  · rintro ⟨w,hw,hv⟩
    have hz : transition c L w ∈ negative.map (LaurentTransitionBounds318.underlying (transition c L)) :=
      ⟨w,hw,rfl⟩
    obtain ⟨b,hb⟩ := (him _).mpr hz
    refine ⟨b,?_⟩
    rw [hb]
    exact hv
  · rintro ⟨b,hb⟩
    have hz : coordinates c L (infinityRestriction c L b) ∈
        negative.map (LaurentTransitionBounds318.underlying (transition c L)) := by
      exact (him _).mp ⟨b,rfl⟩
    obtain ⟨w,hw,he⟩ := hz
    refine ⟨w,hw,?_⟩
    change (LaurentPolynomial.T d : A) • transition c L w = v
    rw [he]
    exact hb

/-- Exact original restriction-difference description of the shifted
boundary, with its genuine Mayer-Vietoris minus sign retained. -/
lemma boundary_iff (v : V ℚ (finiteRank c L)) :
    v ∈ LaurentCechFinite318.boundary
      (LaurentPositiveTwistVanishing318.transition (transition c L) d) ↔
    ∃ (a : finiteSections c L) (b : infinitySections c L),
      coordinates c L (finiteRestriction c L a) -
        (LaurentPolynomial.T d : A) • coordinates c L (infinityRestriction c L b) = v := by
  have hfm (x : V ℚ (finiteRank c L)) :
      (∃ a : finiteSections c L, coordinates c L (finiteRestriction c L a) = x) ↔
        x ∈ positive := Set.ext_iff.mp (finite_image c L) x
  constructor
  · intro hv
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,ha⟩ := (hfm x).mpr hx
    have hny := Submodule.neg_mem _ hy
    obtain ⟨b,hb⟩ := (negative_image c L d (-y)).mp hny
    refine ⟨a,b,?_⟩
    rw [ha,hb,sub_neg_eq_add]
    exact hxy
  · rintro ⟨a,b,rfl⟩
    apply Submodule.sub_mem
    · apply (le_sup_left : positive ≤ LaurentCechFinite318.boundary _)
      exact (hfm _).mp ⟨a,rfl⟩
    · apply (le_sup_right : negative.map _ ≤ LaurentCechFinite318.boundary _)
      exact (negative_image c L d _).mpr ⟨b,rfl⟩
end ContactOriginalShiftedBoundary318
