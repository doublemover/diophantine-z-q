module
public import ResidueRetractionLift318
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public section
noncomputable section
namespace ResidueFiberRetraction318
universe u
open TensorProduct
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

lemma baseChange_injective_of_retraction (m : Ideal R) (n : ℕ)
    (e : (Fin n → R) →ₗ[R] A) (r : A →ₗ[R] (Fin n → R))
    (he : r.comp e = LinearMap.id) :
    Function.Injective (e.baseChange (R ⧸ m)) := by
  apply Function.LeftInverse.injective (g := r.baseChange (R ⧸ m))
  intro x
  have h : (r.baseChange (R ⧸ m)).comp (e.baseChange (R ⧸ m)) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, he, LinearMap.baseChange_id]
  exact LinearMap.congr_fun h x

/-- An injective actual field-fiber map produces a residue retraction
on any specified split finite coordinate span of the original module. -/
lemma exists_retraction (f : A →ₗ[R] B) (m : Ideal R) [m.IsMaximal]
    (hf : Function.Injective (f.baseChange (R ⧸ m)))
    (n : ℕ) (e : (Fin n → R) →ₗ[R] A) (r : A →ₗ[R] (Fin n → R))
    (he : r.comp e = LinearMap.id) :
    ∃ ℓ : B →ₗ[R] (Fin n → R ⧸ m),
      ∀ v, ℓ (f (e v)) = ResidueRetractionLift318.reduce m n v := by
  let K := R ⧸ m
  let p := TensorProduct.piScalarRight R K K (Fin n)
  let E : (Fin n → K) →ₗ[K] K ⊗[R] B :=
    (f.baseChange K).comp ((e.baseChange K).comp p.symm.toLinearMap)
  have hE : Function.Injective E :=
    hf.comp ((baseChange_injective_of_retraction m n e r he).comp p.symm.injective)
  obtain ⟨l, hl⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE)
  let ℓ : B →ₗ[R] (Fin n → K) :=
    (l.restrictScalars R).comp (TensorProduct.mk R K B 1)
  refine ⟨ℓ, ?_⟩
  intro v
  have hp : p ((1 : K) ⊗ₜ[R] v) = ResidueRetractionLift318.reduce m n v := by
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    funext i
    change (v i) • (1 : K) = Ideal.Quotient.mk m (v i)
    rw [Algebra.smul_def, mul_one]
    rfl
  have heval : E (ResidueRetractionLift318.reduce m n v) =
      (1 : K) ⊗ₜ[R] f (e v) := by
    rw [← hp]
    change (f.baseChange K) ((e.baseChange K) (p.symm (p (1 ⊗ₜ[R] v)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul]
  have h := LinearMap.congr_fun hl (ResidueRetractionLift318.reduce m n v)
  change l (E (ResidueRetractionLift318.reduce m n v)) = _ at h
  rw [heval] at h
  exact h
end ResidueFiberRetraction318
