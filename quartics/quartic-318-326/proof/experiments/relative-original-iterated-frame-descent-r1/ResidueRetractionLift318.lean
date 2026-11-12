module
public import FiniteMatrixRetraction318
public import Mathlib.Algebra.Module.Projective
public section
noncomputable section
open scoped Matrix
namespace ResidueRetractionLift318
universe u
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- Literal componentwise reduction to the specified quotient. -/
@[expose] def reduce (m : Ideal R) (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → R ⧸ m) :=
  LinearMap.pi fun i => (Ideal.Quotient.mkₐ R m).toLinearMap.comp (LinearMap.proj i)

lemma reduce_surjective (m : Ideal R) (n : ℕ) :
    Function.Surjective (reduce m n) := by
  intro w
  choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
  exact ⟨v, funext hv⟩

/-- Lift a residue retraction through the actual componentwise quotient
using projectivity of B. The resulting finite matrix is literally the
identity modulo m, so its determinant supplies a genuine scalar witness.
Projectivity is explicit and is NOT inferred from ambient flatness. -/
lemma scalar_witness (f : A →ₗ[R] B) (s : Finset A)
    (m : Ideal R) [m.IsMaximal] [Module.Projective R B]
    (n : ℕ) (e : (Fin n → R) →ₗ[R] A)
    (hs : ∀ a ∈ s, ∃ v, e v = a)
    (ℓ : B →ₗ[R] (Fin n → R ⧸ m))
    (hℓ : ∀ v, ℓ (f (e v)) = reduce m n v) :
    ∃ r ∈ ScalarRetractionIdeal318.scalars f s, r ∉ m := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (reduce m n) ℓ (reduce_surjective m n)
  let T := LinearMap.toMatrix' (g.comp (f.comp e))
  have hT : ∀ v, g (f (e v)) = T *ᵥ v := by
    intro v
    exact (LinearMap.toMatrix'_mulVec (g.comp (f.comp e)) v).symm
  have hres : T.map (Ideal.Quotient.mk m) = 1 := by
    ext i j
    have h := congrArg (fun v => v i)
      (LinearMap.congr_fun hg (f (e (Pi.single j 1))))
    rw [hℓ] at h
    change Ideal.Quotient.mk m ((g (f (e (Pi.single j 1)))) i) =
      Ideal.Quotient.mk m ((Pi.single j (1 : R)) i) at h
    change Ideal.Quotient.mk m ((g (f (e (Pi.single j 1)))) i) =
      (1 : Matrix (Fin n) (Fin n) (R ⧸ m)) i j
    rw [h]
    simp [Matrix.one_apply, Pi.single_apply]
  exact ⟨T.det, FiniteMatrixRetraction318.determinant_mem_scalars f s e g T hs hT,
    FiniteMatrixRetraction318.determinant_not_mem m T hres⟩

/-- Actual residue retractions on finite coordinate spans give the
universal-injectivity input of the flat quotient theorem. Unlike a bare
field-dimension assertion, each retraction includes its comparison with
the original finite-coordinate map. -/
lemma tensor_injective (f : A →ₗ[R] B) [Module.Projective R B]
    (h : ∀ s : Finset A, ∀ m : Ideal R, m.IsMaximal →
      ∃ (n : ℕ) (e : (Fin n → R) →ₗ[R] A)
        (ℓ : B →ₗ[R] (Fin n → R ⧸ m)),
        (∀ a ∈ s, ∃ v, e v = a) ∧
        (∀ v, ℓ (f (e v)) = reduce m n v))
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  apply ScalarRetractionIdeal318.tensor_injective f _ N
  intro s m hm
  letI : m.IsMaximal := hm
  obtain ⟨n, e, ℓ, hs, hℓ⟩ := h s m hm
  exact scalar_witness f s m n e hs ℓ hℓ
end ResidueRetractionLift318
