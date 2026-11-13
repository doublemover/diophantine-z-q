module
public import SurjectiveScalarReduction318
public section
noncomputable section
namespace SquareZeroFramedReduction318
open scoped TensorProduct
universe u v w
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] [Algebra S R]
    (σ : R →+* S) (hσ : ∀ r, algebraMap S R (σ r) = r)
    (e : S) (he : e * e = 0) (hker : RingHom.ker (algebraMap S R) = Ideal.span {e})
    {P : Type w} [AddCommGroup P] [Module S P] [Module.Projective S P]
    (frame : R ⊗[S] P ≃ₗ[R] R)
include hσ in
lemma reduction_surjective : Function.Surjective (algebraMap S R) := fun r => ⟨σ r,hσ r⟩
@[expose] def coefficient : P →ₗ[S] R :=
  (frame.restrictScalars S).toLinearMap.comp (SurjectiveScalarReduction318.reduce P)
lemma coefficient_smul (s : S) (x : P) : coefficient frame (s • x) =
    algebraMap S R s * coefficient frame x := by
  rw [map_smul, Algebra.smul_def]
include hσ in
lemma coefficient_surjective : Function.Surjective (coefficient frame) :=
  frame.surjective.comp (SurjectiveScalarReduction318.reduce_surjective
    (reduction_surjective σ hσ) P)
include hσ hker in
lemma coefficient_kernel (x : P) (hx : coefficient frame x = 0) : ∃ y : P, e • y = x := by
  apply SurjectiveScalarReduction318.epsilon_kernel (reduction_surjective σ hσ) P e hker x
  change frame (SurjectiveScalarReduction318.reduce P x)=0 at hx
  apply frame.injective
  simpa only [map_zero] using hx
include hker in
lemma ring_kernel (s : S) (hs : algebraMap S R s = 0) : ∃ r : S, e * r = s := by
  have hm : s ∈ RingHom.ker (algebraMap S R) := hs
  rw [hker] at hm
  rcases (Ideal.mem_span_singleton').1 hm with ⟨r,hr⟩
  exact ⟨r, (mul_comm e r).trans hr⟩
@[expose] def generator : P := (coefficient_surjective σ hσ frame 1).choose
lemma generator_coefficient : coefficient frame (generator σ hσ frame) = 1 :=
  (coefficient_surjective σ hσ frame 1).choose_spec
/-- Every projective module whose ACTUAL scalar extension is given the supplied
rank-one frame has a genuine basis lifting that frame through this square-zero reduction. -/
@[expose] def equivalence : S ≃ₗ[S] P :=
  SquareZeroProjectiveGenerator318.equivalence (algebraMap S R) σ hσ e he
    (ring_kernel e hker) (coefficient frame).toAddMonoidHom (coefficient_smul frame)
    (coefficient_kernel σ hσ e hker frame) (generator σ hσ frame) (generator_coefficient σ hσ frame)
lemma equivalence_reduces (s : S) :
    coefficient frame (equivalence σ hσ e he hker frame s) = algebraMap S R s := by
  change coefficient frame (s • generator σ hσ frame) = _
  rw [coefficient_smul, generator_coefficient, mul_one]
end SquareZeroFramedReduction318
