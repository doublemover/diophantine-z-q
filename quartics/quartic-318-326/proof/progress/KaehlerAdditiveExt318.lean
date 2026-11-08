module
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace KaehlerAdditiveExt318
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]

/-- Equality on universal differentials extends to the whole Kähler module as
soon as equality is stable under its scalar action. The target need not carry
an independently chosen S-module instance. -/
theorem ext (F G : KaehlerDifferential R S →+ M)
    (hD : ∀ s, F (KaehlerDifferential.D R S s)=G (KaehlerDifferential.D R S s))
    (hsmul : ∀ (s : S) ω, F ω=G ω → F (s • ω)=G (s • ω)) : F=G := by
  apply AddMonoidHom.ext
  intro ω
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨s,rfl⟩
    exact hD s
  · exact (map_zero F).trans (map_zero G).symm
  · intro x y hx hy heqX heqY
    rw [map_add,map_add,heqX,heqY]
  · intro s ω hω heq
    exact hsmul s ω heq
end KaehlerAdditiveExt318
