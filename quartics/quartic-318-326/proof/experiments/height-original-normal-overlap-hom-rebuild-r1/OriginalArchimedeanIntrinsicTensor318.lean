module
public import OriginalArchimedeanCotangentFiber318
public import ContactTrueGlobalTensorPullback318
public section
noncomputable section
namespace OriginalArchimedeanIntrinsicTensor318
open NumberField OriginalPointFinitePlaceRoots318 OriginalArchimedeanSectionCoefficient318
open OriginalArchimedeanCotangentFiber318 AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0)
    (w : InfinitePlace (K c t)) (i : Fin 4)
@[expose] def balanced : Omega c i →ₛₗ[point c t hn w i]
    Omega c i →ₛₗ[point c t hn w i] ℂ where
  toFun ω :=
    { toFun := fun η => differential c t hn w i ω*differential c t hn w i η
      map_add' := fun η ξ => by rw [map_add,mul_add]
      map_smul' := fun a η => by rw [LinearMap.map_smulₛₗ];simp only [smul_eq_mul];ring }
  map_add' ω η := by
    ext ξ
    change differential c t hn w i (ω+η)*_=_
    rw [map_add,add_mul]
    rfl
  map_smul' a ω := by
    ext η
    change differential c t hn w i (a • ω)*_=
      point c t hn w i a • (differential c t hn w i ω*differential c t hn w i η)
    rw [LinearMap.map_smulₛₗ]
    simp only [smul_eq_mul]
    ring

/-- Genuine balanced map on the ENTIRE algebraic cotangent tensor square,
not an operation on a displayed coefficient and chosen pure tensor. -/
@[expose] def tensor : (Omega c i ⊗[A c i] Omega c i) →ₛₗ[point c t hn w i] ℂ :=
  TensorProduct.lift (balanced c t hn w i)
lemma tensor_pure (ω η : Omega c i) : tensor c t hn w i (ω ⊗ₜ[A c i] η)=
    differential c t hn w i ω*differential c t hn w i η := TensorProduct.lift.tmul _ _ _
lemma tensor_coordinate_square : tensor c t hn w i
    (KaehlerDifferential.D ℚ (A c i) (ContactFrameNormalization318.sourceCoordinate c i) ⊗ₜ[A c i]
      KaehlerDifferential.D ℚ (A c i) (ContactFrameNormalization318.sourceCoordinate c i))=
        branchDerivative c t w i^2 := by
  simp only [tensor_pure,differential_coordinate,pow_two]

/-- Start with ANY genuine global intrinsic bicanonical section on the
proper original Q curve, restrict through the actual branch embedding,
then apply the entire balanced analytic tangent functional. -/
@[expose] def globalValue (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) : ℂ :=
  tensor c t hn w i (ContactTrueGlobalTensorPullback318.chartTensor c i s)
lemma globalValue_original (s : Γ(ContactGlobalBicanonical318.tensor c,⊤)) :
    globalValue c t hn w i s=
      w.embedding (ContactBicanonicalPointValue318.value c t hn i s)*branchDerivative c t w i^2 := by
  rw [globalValue,ContactTrueGlobalTensorPullback318.chartTensor,
    IntrinsicFramedTensorSections318.tensor,LinearMap.map_smulₛₗ,tensor_coordinate_square]
  rfl
lemma globalValue_scaled0 : globalValue c t hn w i (ContactScaledBicanonicalPoint318.scaledQ0 c)=
    (2765952000:ℂ)^2*BicanonicalCharts318.q0 LiteralMetricExtension318.contacts (t:ℂ) := by
  rw [globalValue_original]
  exact (scaled_coordinates c t hn w i).1
lemma globalValue_scaled1 : globalValue c t hn w i (ContactScaledBicanonicalPoint318.scaledQ1 c)=
    (2765952000:ℂ)^2*BicanonicalCharts318.q1 LiteralMetricExtension318.contacts (t:ℂ) := by
  rw [globalValue_original]
  exact (scaled_coordinates c t hn w i).2
end OriginalArchimedeanIntrinsicTensor318
