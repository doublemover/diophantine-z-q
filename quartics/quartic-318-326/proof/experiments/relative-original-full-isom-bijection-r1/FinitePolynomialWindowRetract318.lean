module
public import PolynomialCoefficientWindow318
public section
noncomputable section
namespace FinitePolynomialWindowRetract318
open FiniteLaurentVectorFiltration318
universe u v
variable (R : Type u) [CommRing R] (H : Type v) [AddCommGroup H] [Module R H]
  (r s : ℕ)
  (out : H →ₗ[R] ((Fin r → Polynomial R) × (Fin s → Polynomial R)))
  (back : ((Fin r → Polynomial R) × (Fin s → Polynomial R)) →ₗ[R] H)
  (h : back.comp out = LinearMap.id) (b d : ℕ)
  (h0 : ∀ x : H, (fun i => Polynomial.toLaurent ((out x).1 i)) ∈
    (upper (b : ℤ) : Submodule R (V R (Fin r))))
  (h1 : ∀ x : H, (fun i => Polynomial.toLaurent ((out x).2 i)) ∈
    (upper (d : ℤ) : Submodule R (V R (Fin s))))

@[expose] def finiteOut : H →ₗ[R] ((Fin r → Fin (b+1) → R) × (Fin s → Fin (d+1) → R)) :=
  ((PolynomialCoefficientWindow318.encode R r b).prodMap
    (PolynomialCoefficientWindow318.encode R s d)).comp out
@[expose] def finiteBack : ((Fin r → Fin (b+1) → R) × (Fin s → Fin (d+1) → R)) →ₗ[R] H :=
  back.comp ((PolynomialCoefficientWindow318.decode R r b).prodMap
    (PolynomialCoefficientWindow318.decode R s d))

include h h0 h1 in
/-- A split original polynomial presentation with ACTUALLY produced
bounds restricts to a genuine finite free retract. Merely embedding a
projective module in a finite free module would not suffice. -/
lemma retract : (finiteBack R H r s back b d).comp (finiteOut R H r s out b d) = LinearMap.id := by
  ext x
  change back (PolynomialCoefficientWindow318.decode R r b
      (PolynomialCoefficientWindow318.encode R r b (out x).1),
    PolynomialCoefficientWindow318.decode R s d
      (PolynomialCoefficientWindow318.encode R s d (out x).2)) = x
  rw [PolynomialCoefficientWindow318.decode_encode R r b (out x).1 (h0 x),
    PolynomialCoefficientWindow318.decode_encode R s d (out x).2 (h1 x)]
  exact LinearMap.congr_fun h x

include h h0 h1 in
/-- Both finite generation and projectivity are produced by the actual
finite retract. This is valid without Noetherian/coherence assumptions. -/
theorem finite_projective : Module.Finite R H ∧ Module.Projective R H := by
  have hr := retract R H r s out back h b d h0 h1
  have hf : Function.Surjective (finiteBack R H r s back b d) := by
    intro x
    exact ⟨finiteOut R H r s out b d x,LinearMap.congr_fun hr x⟩
  exact ⟨Module.Finite.of_surjective _ hf,
    Module.Projective.of_split (finiteOut R H r s out b d) (finiteBack R H r s back b d) hr⟩
end FinitePolynomialWindowRetract318
