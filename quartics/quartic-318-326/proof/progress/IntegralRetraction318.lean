module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.RingHom.Integral
public section
noncomputable section
namespace IntegralRetraction318
variable {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S]

/-- An integral extension which is a domain admits no nontrivial retraction kernel. -/
theorem retraction_injective (f : R →+* S) (g : S →+* R)
    (hf : f.IsIntegral) (hgf : g.comp f = RingHom.id R) : Function.Injective g := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hf⟩
  apply (RingHom.injective_iff_ker_eq_bot g).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := R)
  change Ideal.comap f (RingHom.ker g) = ⊥
  ext x
  change g (f x) = 0 ↔ x = 0
  rw [show g (f x) = x from RingHom.congr_fun hgf x]

/-- An integral ring map into a domain with a section back is bijective. -/
theorem bijective (f : R →+* S) (g : S →+* R)
    (hf : f.IsIntegral) (hgf : g.comp f = RingHom.id R) : Function.Bijective f := by
  have h (r : R) : g (f r) = r := RingHom.congr_fun hgf r
  refine ⟨fun a b hab => (h a).symm.trans ((congrArg g hab).trans (h b)), ?_⟩
  intro s
  refine ⟨g s, retraction_injective f g hf hgf ?_⟩
  exact h (g s)

/-- The actual integral extension equals the base, with the given retraction as inverse. -/
def ringEquiv (f : R →+* S) (g : S →+* R)
    (hf : f.IsIntegral) (hgf : g.comp f = RingHom.id R) : R ≃+* S :=
  RingEquiv.ofBijective f (bijective f g hf hgf)
end IntegralRetraction318
