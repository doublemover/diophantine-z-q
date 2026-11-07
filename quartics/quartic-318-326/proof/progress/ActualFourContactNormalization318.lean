module
public import FourContactNormalization318
public import FourContactBranches318
public section
noncomputable section
namespace ActualFourContactNormalization318
set_option maxHeartbeats 500000
open scoped TensorProduct
open FourUnitCover318
variable {R K:Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (f:Fin 4→R)
abbrev Raw:=(QuadraticPresentation318.RootRing (f 0)⊗[R]QuadraticPresentation318.RootRing (f 1))⊗[R]
  (QuadraticPresentation318.RootRing (f 2)⊗[R]QuadraticPresentation318.RootRing (f 3))

@[expose] def intoGeneric {u:Fin 4→Rˣ} (φ:Raw f→ₐ[R]Cover u) : Raw f→ₐ[R]Cover u⊗[R]K :=
  Algebra.TensorProduct.includeLeft.comp φ
@[expose,instance_reducible] def genericAlgebra {u:Fin 4→Rˣ} (φ:Raw f→ₐ[R]Cover u) :
    Algebra (Raw f) (Cover u⊗[R]K) :=
  RingHom.toAlgebra (R:=Raw f) (S:=Cover u⊗[R]K) (intoGeneric (K:=K) f φ).toRingHom

/-- The exact raw order of four original inputs is normalized by a constructed
rank-sixteen etale cover. Only the actual canonical even values and invertible
2 are supplied; the common uniformizer, units, maps and generic equivalence
are derived, including split and repeated factors. -/
theorem actual_four_normalization [IsDiscreteValuationRing R]
    (m:Fin 4→ℕ) (h2:IsUnit (2:R))
    (hv:∀i,IsDiscreteValuationRing.addVal R (f i)=((2*m i:ℕ):ℕ∞)) :
    ∃(u:Fin 4→Rˣ)(pi:R)(φ:Raw f→ₐ[R]Cover u),
      Irreducible pi ∧ (∀i,f i=(u i:R)*pi^(2*m i)) ∧
      letI:=genericAlgebra (K:=K) f φ
      IsIntegralClosure (Cover u) (Raw f) (Cover u⊗[R]K) ∧
      Algebra.Etale R (Cover u) ∧ Module.Finite R (Cover u) ∧
      Module.finrank R (Cover u)=16 ∧ Module.finrank R (Raw f)=16 ∧
      Function.Injective (intoGeneric (K:=K) f φ) ∧
      ∃e:K⊗[R]Raw f≃ₐ[R]Cover u⊗[R]K,∀x,e (1⊗ₜ[R]x)=intoGeneric f φ x := by
  obtain ⟨u,pi,hpi,hf⟩:=FourContactBranches318.common_decomposition f m hv
  have hfun:f=(fun i=>(u i:R)*pi^(2*m i)):=funext hf
  subst f
  refine ⟨u,pi,FourContactOrder318.orderMap u pi m,hpi,(fun _=>rfl),?_⟩
  exact FourContactNormalization318.normalized_four_contacts u pi m h2 hpi.ne_zero
end ActualFourContactNormalization318
