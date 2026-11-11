module
public import SchemeClosedOpenPushout318
public section
noncomputable section
namespace SchemeTwoOpenClosedDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y B : Scheme.{u}} (i : X ⟶ B) (j : Y ⟶ B)
  [IsOpenImmersion i] [IsOpenImmersion j] (h : i.opensRange ⊔ j.opensRange=⊤)
@[expose] def cover : B.OpenCover where
  I₀ := Bool
  X b := if b then Y else X
  f b := by cases b; exact i; exact j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      have hz : z∈i.opensRange ⊔ j.opensRange := by rw [h]; trivial
      rcases hz with ⟨x,hx⟩|⟨y,hy⟩
      · exact ⟨false,x,hx⟩
      · exact ⟨true,y,hy⟩
    · intro b
      cases b <;> infer_instance
variable {Z P Q : Scheme.{u}} (m : Z ⟶ B) (a : P ⟶ Z) (b : Q ⟶ Z)
  (p : P ⟶ X) (q : Q ⟶ Y) [IsClosedImmersion p] [IsClosedImmersion q]
  (ha : IsPullback a p m i) (hb : IsPullback b q m j)
/-- Closedness descends from the actual full two-chart pullbacks. -/
lemma closed : IsClosedImmersion m := by
  apply IsZariskiLocalAtTarget.of_openCover (cover i j h)
  intro k
  cases k with
  | false =>
    have hc : IsClosedImmersion (ha.isoPullback.inv ≫ p) := inferInstance
    simpa only [ha.isoPullback_inv_snd] using hc
  | true =>
    have hc : IsClosedImmersion (hb.isoPullback.inv ≫ q) := inferInstance
    simpa only [hb.isoPullback_inv_snd] using hc
end SchemeTwoOpenClosedDescent318
