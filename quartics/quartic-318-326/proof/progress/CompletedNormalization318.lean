module
public import ContactTensor318
public import IntegralClosureTransport318
public import CompletionDescent318
public section
noncomputable section
namespace CompletedNormalization318
set_option maxHeartbeats 900000
open scoped TensorProduct
open ContactTensor318
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

abbrev C:=ActualDVRCompletion318.Completion R
abbrev Order (u:Rˣ) (pi:R) (m:ℕ):=C (R:=R)⊗[R]
  QuadraticPresentation318.RootRing ((u:R)*pi^(2*m))
abbrev Normalization (u:Rˣ):=C (R:=R)⊗[R]EvenContactEtale318.RootRing u
abbrev Ambient (u:Rˣ):=EvenContactEtale318.RootRing (mappedUnit (S:=C (R:=R)) u)
  ⊗[C (R:=R)]FractionRing (C (R:=R))

@[expose] def orderMap (u:Rˣ) (pi:R) (m:ℕ) : Order u pi m→ₐ[C (R:=R)]Ambient u :=
  (NormalizedContactOrder318.orderToGeneric (mappedUnit u) (algebraMap R (C (R:=R)) pi) m).comp
    (orderBaseChange u pi m).toAlgHom

@[expose] def normalizationMap (u:Rˣ) : Normalization u→ₐ[C (R:=R)]Ambient u :=
  Algebra.TensorProduct.includeLeft.comp (unitBaseChange u).toAlgHom

/-- The order and normalization maps are the actual scalar base changes of
the original contact map, followed by the actual generic-fiber inclusion. -/
theorem map_compatibility (u:Rˣ) (pi:R) (m:ℕ) :
    (normalizationMap u).comp (tensorContact u pi m)=orderMap u pi m := by
  apply AlgHom.ext
  intro z
  have h:=AlgHom.congr_fun (contact_square (S:=C (R:=R)) u pi m) z
  exact congrArg (algebraMap
    (EvenContactEtale318.RootRing (mappedUnit (S:=C (R:=R)) u)) (Ambient u)) h

/-- The base change of the actual even-contact normalization to the actual
faithfully flat DVR completion is the integral closure of the actual base-changed
contact order. No general normalization/complete-base-change theorem is assumed. -/
theorem completion_integralClosure (u:Rˣ) (pi:R) (m:ℕ) (h2:IsUnit (2:R)) :
    letI:Algebra (Order u pi m) (Ambient u):=(orderMap u pi m).toRingHom.toAlgebra
    letI:Algebra (Normalization u) (Ambient u):=(normalizationMap u).toRingHom.toAlgebra
    IsIntegralClosure (Normalization u) (Order u pi m) (Ambient u) := by
  letI:Algebra (Order u pi m) (Ambient u):=(orderMap u pi m).toRingHom.toAlgebra
  letI:Algebra (Normalization u) (Ambient u):=(normalizationMap u).toRingHom.toAlgebra
  letI:=NormalizedContactOrder318.orderAlgebra (K:=FractionRing (C (R:=R)))
    (mappedUnit (S:=C (R:=R)) u) (algebraMap R (C (R:=R)) pi) m
  have h2c:IsUnit (2:C (R:=R)):=by
    simpa only [map_ofNat] using h2.map (algebraMap R (C (R:=R)))
  letI:=NormalizedContactOrder318.integralClosure (K:=FractionRing (C (R:=R)))
    (mappedUnit (S:=C (R:=R)) u) (algebraMap R (C (R:=R)) pi) m h2c
  apply IntegralClosureTransport318.transport
    (orderBaseChange (S:=C (R:=R)) u pi m).toRingEquiv
    (unitBaseChange (S:=C (R:=R)) u).toRingEquiv
  · rfl
  · intro a
    rfl

/-- The actual generic fiber of the completed order is isomorphic to the
ambient algebra used in the integral-closure theorem, with no domain assertion
for the quadratic algebra. -/
@[expose] def genericEquiv (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) :
    FractionRing (C (R:=R)) ⊗[C (R:=R)] Order u pi m ≃ₐ[C (R:=R)] Ambient u :=
  ((Algebra.TensorProduct.congr
    (AlgEquiv.refl : FractionRing (C (R:=R)) ≃ₐ[FractionRing (C (R:=R))]
      FractionRing (C (R:=R))) (orderBaseChange (S:=C (R:=R)) u pi m)).restrictScalars
        (C (R:=R))).trans
    (NormalizedContactOrder318.genericOrderEquiv (mappedUnit (S:=C (R:=R)) u)
      (algebraMap R (C (R:=R)) pi) m
      (by simpa only [map_zero] using (ActualDVRCompletion318.completion_injective R).ne hp))

theorem genericEquiv_on_order (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) (z:Order u pi m) :
    genericEquiv u pi m hp (1⊗ₜ[C (R:=R)]z)=orderMap u pi m z := by
  simp only [genericEquiv,AlgEquiv.trans_apply,AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom,map_one,NormalizedContactOrder318.genericOrderEquiv_on_order]
  rfl

theorem orderMap_injective (u:Rˣ) (pi:R) (m:ℕ) (hp:pi≠0) :
    Function.Injective (orderMap u pi m) := by
  exact (NormalizedContactOrder318.orderToGeneric_injective (mappedUnit (S:=C (R:=R)) u)
    (algebraMap R (C (R:=R)) pi) m
    (by simpa only [map_zero] using (ActualDVRCompletion318.completion_injective R).ne hp)).comp
      (orderBaseChange (S:=C (R:=R)) u pi m).injective

/-- The completed normalization is genuinely finite etale, and completion is
faithfully flat over the original DVR. -/
theorem completion_etale (u:Rˣ) (h2:IsUnit (2:R)) :
    Algebra.Etale (C (R:=R)) (Normalization u) ∧
      Module.Finite (C (R:=R)) (Normalization u) ∧
      Module.FaithfullyFlat R (C (R:=R)) := by
  letI:=EvenContactEtale318.rootRing_etale u h2
  letI:=EvenContactEtale318.rootRing_finite u
  exact ⟨inferInstance,inferInstance,CompletionDescent318.completion_faithfullyFlat R⟩

end CompletedNormalization318
