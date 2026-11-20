module
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section

namespace CTLocalOrderUnramified318

/-- If a local image order B_q is generated before localization by an
unramified old integer chart over the new scalars, the localized order
is formally unramified over the new scalars. The old map was localized
at the same selected place; no global surjectivity to the new order. -/
theorem localized_image_order_formallyUnramified
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R B]
    (P : Ideal A) [P.IsPrime] [Algebra.IsUnramifiedAt ℤ P]
    (q : Ideal B) [q.IsPrime]
    (a : A →+* B) (l : Localization.AtPrime P →ₐ[ℤ] Localization.AtPrime q)
    (hl : ∀ x : A, l (algebraMap A (Localization.AtPrime P) x) =
      algebraMap B (Localization.AtPrime q) (a x))
    (hgen : Algebra.adjoin R (Set.range a) = ⊤) :
    Algebra.FormallyUnramified R (Localization.AtPrime q) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro T _ _ I hI f g hfg
  have he : (f.restrictScalars ℤ).comp l = (g.restrictScalars ℤ).comp l := by
    apply Algebra.FormallyUnramified.comp_injective I hI
    apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hfg (l x)
    change Ideal.Quotient.mk I (f (l x)) = Ideal.Quotient.mk I (g (l x)) at hx ⊢
    exact hx
  apply IsLocalization.algHom_ext q.primeCompl
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨x,rfl⟩
  change f (algebraMap B (Localization.AtPrime q) (a x)) =
    g (algebraMap B (Localization.AtPrime q) (a x))
  rw [← hl]
  exact DFunLike.congr_fun he (algebraMap A (Localization.AtPrime P) x)

end CTLocalOrderUnramified318
