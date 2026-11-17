module
public import GenericOpenPushout318
public section
noncomputable section
namespace OpenPushoutChartPreimage318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U X Y A T : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- The two actual open pushout charts cover, with no assumed cover witness. -/
theorem charts_cover (x : pushout f g) :
    (∃ p, pushout.inl f g p = x) ∨ (∃ q, pushout.inr f g q = x) := by
  obtain ⟨i, q, hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  cases i with
  | none =>
    left
    refine ⟨f q, ?_⟩
    change (f ≫ pushout.inl f g) q = x
    rw [show f ≫ pushout.inl f g = colimit.ι (span f g) WalkingSpan.zero from
      colimit.w (span f g) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q, hq⟩
    | right => exact Or.inr ⟨q, hq⟩

/-- Exact cross-chart preimage, together with the actual restriction squares,
identifies the ENTIRE preimage of a target chart. Chartwise finiteness alone
would not establish this hypothesis or conclusion. -/
theorem preimage (φ : pushout f g ⟶ T) (i : A ⟶ T) [IsOpenImmersion i]
    (a : X ⟶ A) (b : Y ⟶ T)
    (hleft : pushout.inl f g ≫ φ = a ≫ i)
    (hright : pushout.inr f g ≫ φ = b)
    (hcross : b ⁻¹ᵁ i.opensRange = g.opensRange) :
    φ ⁻¹ᵁ i.opensRange = (pushout.inl f g).opensRange := by
  ext x
  change (φ x ∈ Set.range i) ↔ x ∈ Set.range (pushout.inl f g)
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := charts_cover f g x
    · exact ⟨p, rfl⟩
    · have hq : q ∈ b ⁻¹ᵁ i.opensRange := by
        change b q ∈ Set.range i
        have h := congrArg (fun k => k q) hright
        exact h ▸ hx
      rw [hcross] at hq
      obtain ⟨z, hz⟩ := hq
      refine ⟨f z, ?_⟩
      calc
        pushout.inl f g (f z) = pushout.inr f g (g z) :=
          congrArg (fun k => k z) (pushout.condition (f := f) (g := g))
        _ = pushout.inr f g q := congrArg (pushout.inr f g) hz
  · rintro ⟨p, rfl⟩
    have h := congrArg (fun k => k p) hleft
    change φ (pushout.inl f g p) = i (a p) at h
    rw [h]
    exact ⟨a p, rfl⟩

/-- The local map is the actual categorical pullback over the target chart,
so a target-local morphism property may be transported without replacing a
whole preimage by a smaller source open. -/
theorem square (φ : pushout f g ⟶ T) (i : A ⟶ T) [IsOpenImmersion i]
    (a : X ⟶ A) (b : Y ⟶ T)
    (hleft : pushout.inl f g ≫ φ = a ≫ i)
    (hright : pushout.inr f g ≫ φ = b)
    (hcross : b ⁻¹ᵁ i.opensRange = g.opensRange) :
    IsPullback a (pushout.inl f g) i φ := by
  apply IsOpenImmersion.isPullback
  · exact hleft
  · exact preimage f g φ i a b hleft hright hcross

end OpenPushoutChartPreimage318
