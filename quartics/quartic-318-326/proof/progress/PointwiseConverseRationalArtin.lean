module
public import PointwiseConverseCochainFiniteNormalFactor
public import PointwiseConverseMatchedInnerOuter
public import Mathlib.FieldTheory.AbsoluteGaloisGroup

@[expose] public section
noncomputable section

open PointwiseConverseRawMatrixReceiver PointwiseConverseCochainFiniteNormalFactor
open PointwiseConverseMatchedInnerOuter Filter

namespace PointwiseConverseRationalArtin

variable {Ω : Type*} [Field Ω] [CharZero Ω] [hΩ : IsGalois ℚ Ω]
variable (K : IntermediateField ℚ Ω) [hKfin : FiniteDimensional ℚ K] [hKgal : IsGalois K Ω]

/-- Relative automorphisms acting on the *same* closure, with scalars forgotten. -/
abbrev ratAut : Gal(Ω/K) →* Gal(Ω/ℚ) := AlgEquiv.restrictScalarsHom ℚ

/-- Restriction to a genuine finite rational Galois extension. -/
abbrev res (D : FiniteGaloisIntermediateField ℚ Ω) : Gal(Ω/ℚ) →* Gal(D/ℚ) :=
  AlgEquiv.restrictNormalHom D

include hΩ hKfin in
omit hKgal in
/-- Take a finite rational normal field containing both the old cochain
field and the specified extra rational Artin fields (their compositum).
The old field need not itself be normal over ℚ. -/
theorem exists_ambient (E : FiniteGaloisIntermediateField K Ω)
    (X : IntermediateField ℚ Ω) [FiniteDimensional ℚ X] :
    ∃ D : FiniteGaloisIntermediateField ℚ Ω,
      E.toIntermediateField.restrictScalars ℚ ≤ D.toIntermediateField ∧
      X ≤ D.toIntermediateField := by
  let E₀ := E.toIntermediateField.restrictScalars ℚ
  let : FiniteDimensional ℚ E := Module.Finite.trans K E
  let e₀ : E ≃+* E₀ :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let e : E ≃ₐ[ℚ] E₀ := { e₀ with commutes' := e₀.toRingHom.map_rat_algebraMap }
  let : FiniteDimensional ℚ E₀ := e.toLinearEquiv.finiteDimensional
  let A := E₀ ⊔ X
  let : FiniteDimensional ℚ A := IntermediateField.finiteDimensional_sup E₀ X
  let M := IntermediateField.normalClosure ℚ A Ω
  let : FiniteDimensional ℚ M := normalClosure.is_finiteDimensional ℚ A Ω
  let : Normal ℚ M := normalClosure.normal ℚ A Ω
  let D : FiniteGaloisIntermediateField ℚ Ω :=
    { toIntermediateField := M, isGalois := ⟨⟩ }
  have hAM : A ≤ M := A.le_normalClosure
  exact ⟨D, (show E₀ ≤ A from le_sup_left).trans hAM,
    (show X ≤ A from le_sup_right).trans hAM⟩

omit hΩ hKfin in
/-- Equality in the rational quotient refines equality in the original
relative cochain quotient. In particular equality up to conjugacy alone
is *not* enough for this step. -/
theorem relative_coset_eq (E : FiniteGaloisIntermediateField K Ω)
    (D : FiniteGaloisIntermediateField ℚ Ω)
    (hED : E.toIntermediateField.restrictScalars ℚ ≤ D.toIntermediateField)
    (a b : Gal(Ω/K)) (hab : res D (ratAut K a) = res D (ratAut K b)) :
    (a : Gal(Ω/K) ⧸ E.fixingSubgroup) = (b : Gal(Ω/K) ⧸ E.fixingSubgroup) := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  have he : res D (ratAut K (a / b)) = 1 := by
    simp only [map_div, hab]
    rw [div_eq_mul_inv, mul_inv_cancel]
  have hfix := (AlgEquiv.restrictNormal_eq_one_iff D.toIntermediateField
    (ratAut K (a / b))).mp he
  apply (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField (a / b)).mpr
  exact fun x hx => hfix x (hED hx)

include hΩ hKfin hKgal in
/-- The *whole* retained packet factors on actual pairs of G_K elements
through restriction to one finite rational field. This avoids assigning
arbitrary values to cosets outside the relative image. -/
theorem raw_ambient_control (S : Shape) (i : ℕ)
    (f : (Gal(Ω/K) × Gal(Ω/K)) → Packet S i)
    (hf : ∀ m a b d, IsLocallyConstant (fun x => f x m a b d))
    (X : IntermediateField ℚ Ω) [FiniteDimensional ℚ X] :
    ∃ D : FiniteGaloisIntermediateField ℚ Ω, X ≤ D.toIntermediateField ∧
      (∀ g h g' h' : Gal(Ω/K),
        res D (ratAut K g) = res D (ratAut K g') →
        res D (ratAut K h) = res D (ratAut K h') →
        f (g,h) = f (g',h')) := by
  obtain ⟨E, _, fbar, he⟩ := raw_packet_factors_finite_galois S i f hf
  obtain ⟨D,hED,hXD⟩ := exists_ambient K E X
  refine ⟨D, hXD, ?_⟩
  intro g h g' h' hg hh
  rw [← he g h, ← he g' h', relative_coset_eq K E D hED g g' hg,
    relative_coset_eq K E D hED h h' hh]

omit hΩ hKfin hKgal in
/-- Test the square in G_K by its actual rational representative. The
second cochain argument has been retained independently (e.g. an old
slot or a tame generator), so it is not silently replaced by the square. -/
theorem square_packet_eq (S : Shape) (i : ℕ)
    (f : (Gal(Ω/K) × Gal(Ω/K)) → Packet S i)
    (D : FiniteGaloisIntermediateField ℚ Ω)
    (hD : ∀ g h g' h' : Gal(Ω/K),
        res D (ratAut K g) = res D (ratAut K g') →
        res D (ratAut K h) = res D (ratAut K h') → f (g,h) = f (g',h'))
    (γ target : Gal(Ω/ℚ)) (sq targetSq h h' : Gal(Ω/K))
    (hsq : ratAut K sq = γ ^ 2) (htar : ratAut K targetSq = target ^ 2)
    (hγ : res D γ = res D target)
    (hh : res D (ratAut K h) = res D (ratAut K h')) :
    f (sq,h) = f (targetSq,h') := by
  apply hD _ _ _ _ _ hh
  rw [hsq, htar, map_pow, map_pow, hγ]

end PointwiseConverseRationalArtin
