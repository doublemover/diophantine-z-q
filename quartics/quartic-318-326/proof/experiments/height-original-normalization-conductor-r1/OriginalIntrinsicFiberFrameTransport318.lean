module
public import OriginalGlobalFrameTransport318
public import OriginalIntrinsicFiniteLattices318
public section
noncomputable section
namespace OriginalIntrinsicFiberFrameTransport318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry
open OriginalArithmeticTensorFiber318 ContactBicanonicalPointHeight318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i j : Fin 4)

/-- Both-inverse transport of the actual arithmetic tensor fibers with
the scalar PROVED to be the actual original point-sheaf frame transition. -/
@[expose] def comparison : fiber c t hn i ≃ₗ[K c t] fiber c t hn j :=
  frame c t hn i ≪≫ₗ
    LinearEquiv.smulOfUnit (Units.mk0 (frameScalar c t hn i j) (frameScalar_ne c t hn i j)) ≪≫ₗ
      (frame c t hn j).symm
lemma frame_comparison (x : fiber c t hn i) :
    frame c t hn j (comparison c t hn i j x)=frameScalar c t hn i j*frame c t hn i x :=
  (frame c t hn j).apply_symm_apply _

/-- ALL genuine global sections commute with this full fiber comparison,
using the categorical whole-point normalization, not only q0/q1 ratios. -/
lemma comparison_global (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    comparison c t hn i j (globalFiber c t hn i s)=globalFiber c t hn j s := by
  apply (frame c t hn j).injective
  rw [frame_comparison,frame_globalFiber,frame_globalFiber,
    OriginalGlobalFrameTransport318.value_transition c t hn i j s]

section AllPlaces
open OriginalAllPlaceProducedNorms318 ActualFinitePlaceIntegers318
variable (u v : ℤ) (hf : ∀ k : Fin 5,ContactRadical318.forms u v k≠0)
  (w : FinitePlace (OriginalAllPlaceProducedNorms318.K c u v))
local notation "t₀" => OriginalAllPlaceProducedNorms318.t u v
local notation "hn₀" => OriginalAllPlaceProducedNorms318.hn c u v hf
local notation "R" => Integers w
local instance (k : Fin 4) : Module R (fiber c t₀ hn₀ k) :=
  Module.compHom _ (algebraMap R (OriginalAllPlaceProducedNorms318.K c u v))
local instance (k : Fin 4) : IsScalarTower R (OriginalAllPlaceProducedNorms318.K c u v)
    (fiber c t₀ hn₀ k) := IsScalarTower.of_compHom ..

lemma finite_normalizer_transition :
    (w (OriginalIntrinsicFiniteLattices318.normalizer c u v hf j w))⁻¹=
      (w (frameScalar c t₀ hn₀ i j))⁻¹*
        (w (OriginalIntrinsicFiniteLattices318.normalizer c u v hf i w))⁻¹ := by
  rw [←OriginalIntrinsicFiniteLattices318.assembled_norm c u v hf j w,
    ←OriginalIntrinsicFiniteLattices318.assembled_norm c u v hf i w]
  by_cases hw : w (ContactArithmeticDenominator318.denominator c:
      OriginalAllPlaceProducedNorms318.K c u v)=1
  · simp only [OriginalFiniteNormAssembly318.finiteNorm,dif_pos hw]
    exact OriginalGoodLatticeFrameChange318.norm_transition c t₀ hn₀ w hw i j
  · simp only [OriginalFiniteNormAssembly318.finiteNorm,dif_neg hw]
    exact OriginalAllPlaceFrameCoherence318.excluded_norm_transition c u v hf i j ⟨w,hw⟩

/-- The full actual embedded integral lattices, including every bad
prime, are carried to each other by the SAME whole arithmetic fiber map. -/
theorem lattice_transport :
    (OriginalIntrinsicFiniteLattices318.lattice c u v hf j w).comap
      ((comparison c t₀ hn₀ i j).restrictScalars R).toLinearMap=
        OriginalIntrinsicFiniteLattices318.lattice c u v hf i w := by
  apply Submodule.ext
  intro x
  change comparison c t₀ hn₀ i j x∈OriginalIntrinsicFiniteLattices318.lattice c u v hf j w ↔ _
  rw [OriginalIntrinsicFiniteLattices318.mem_iff,OriginalIntrinsicFiniteLattices318.mem_iff,
    frame_comparison,map_mul,finite_normalizer_transition c i j u v hf w]
  have hs : w (frameScalar c t₀ hn₀ i j)≠0 := (w.pos (frameScalar_ne c t₀ hn₀ i j)).ne'
  have he : (w (frameScalar c t₀ hn₀ i j)*w (frame c t₀ hn₀ i x))*
      ((w (frameScalar c t₀ hn₀ i j))⁻¹*
        (w (OriginalIntrinsicFiniteLattices318.normalizer c u v hf i w))⁻¹)=
      w (frame c t₀ hn₀ i x)*(w (OriginalIntrinsicFiniteLattices318.normalizer c u v hf i w))⁻¹ := by
    calc
      _ = (w (frameScalar c t₀ hn₀ i j)*(w (frameScalar c t₀ hn₀ i j))⁻¹)*
        (w (frame c t₀ hn₀ i x)*(w (OriginalIntrinsicFiniteLattices318.normalizer c u v hf i w))⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hs,one_mul]
  rw [he]
end AllPlaces
end OriginalIntrinsicFiberFrameTransport318
