module
public import FractionDerivation318
public import KaehlerFrame318
public section
noncomputable section
namespace FractionKaehlerFrame318
open KaehlerDifferential KaehlerFrame318
set_option maxHeartbeats 100000
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]

@[expose] def derived (integral : KaehlerDifferential R B ≃ₗ[B] B) : Derivation R K K :=
  FractionDerivation318.extend (frameDerivation integral)

/-- The actual fraction-field universal differential functional extends the integral frame. -/
theorem lift_on_map (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (ω : KaehlerDifferential R B) :
    (derived (K := K) integral).liftKaehlerDifferential (KaehlerDifferential.map R R B K ω) =
      algebraMap B K (integral ω) := by
  have h : ((derived (K := K) integral).liftKaehlerDifferential.restrictScalars B).comp
        (KaehlerDifferential.map R R B K) =
      (Algebra.linearMap B K).comp integral.toLinearMap := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    change (derived (K := K) integral).liftKaehlerDifferential
      (KaehlerDifferential.map R R B K (KaehlerDifferential.D R B b)) =
        algebraMap B K (integral (KaehlerDifferential.D R B b))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
    exact FractionDerivation318.extend_integral (frameDerivation integral) b
  exact congrArg (fun f : KaehlerDifferential R B →ₗ[B] K => f ω) h

/-- The mapped integral frame generator cannot vanish: the actual functional sends it to one. -/
theorem mapped_generator_ne_zero (integral : KaehlerDifferential R B ≃ₗ[B] B) :
    KaehlerDifferential.map R R B K (integral.symm 1) ≠ 0 := by
  intro h
  have hh := lift_on_map (K := K) integral (integral.symm 1)
  simp [h] at hh

/-- Every actual generic differential is a scalar multiple of the mapped integral generator. -/
theorem generic_spanned (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (ω : KaehlerDifferential R K) :
    ω ∈ Submodule.span K ({KaehlerDifferential.map R R B K (integral.symm 1)} :
      Set (KaehlerDifferential R K)) := by
  let S := Submodule.span K ({KaehlerDifferential.map R R B K (integral.symm 1)} :
      Set (KaehlerDifferential R K))
  have hi (b : B) : KaehlerDifferential.D R K (algebraMap B K b) ∈ S := by
    rw [← KaehlerDifferential.map_D R R B K]
    have hw : KaehlerDifferential.D R B b = integral (KaehlerDifferential.D R B b) • integral.symm 1 := by
      apply integral.injective
      simp
    rw [hw, LinearMap.map_smul, ←IsScalarTower.algebraMap_smul K]
    exact S.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  have hx (x : K) : KaehlerDifferential.D R K x ∈ S := by
    obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective B x
    rw [(KaehlerDifferential.D R K).leibniz_div]
    exact S.smul_mem _ (S.sub_mem (S.smul_mem _ (hi a)) (S.smul_mem _ (hi b)))
  have hh : Submodule.span K (Set.range (KaehlerDifferential.D R K)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hx x
  rw [KaehlerDifferential.span_range_derivation] at hh
  exact hh (Submodule.mem_top)

/-- The generic functional is a genuine isomorphism, not an assumed generic frame. -/
theorem lift_bijective (integral : KaehlerDifferential R B ≃ₗ[B] B) :
    Function.Bijective (derived (K := K) integral).liftKaehlerDifferential := by
  let L := (derived (K := K) integral).liftKaehlerDifferential
  let w := KaehlerDifferential.map R R B K (integral.symm 1)
  have hw : L w = 1 := by simpa [L,w] using lift_on_map (K := K) integral (integral.symm 1)
  have he (ω : KaehlerDifferential R K) : ω = L ω • w := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (generic_spanned integral ω)
    rw [←ha, map_smul, hw, smul_eq_mul, mul_one]
  constructor
  · intro x y hxy
    rw [he x,he y,hxy]
  · intro a
    exact ⟨a • w,by rw [map_smul,hw,smul_eq_mul,mul_one]⟩

/-- The generic Kähler frame is constructed from the actual integral one. -/
@[expose] def genericFrame (integral : KaehlerDifferential R B ≃ₗ[B] B) :
    KaehlerDifferential R K ≃ₗ[K] K :=
  LinearEquiv.ofBijective (derived (K := K) integral).liftKaehlerDifferential (lift_bijective (K := K) integral)

theorem genericFrame_generator (integral : KaehlerDifferential R B ≃ₗ[B] B) :
    genericFrame (K := K) integral (KaehlerDifferential.map R R B K (integral.symm 1)) = 1 := by
  change (derived (K := K) integral).liftKaehlerDifferential _ = _
  simpa using lift_on_map (K := K) integral (integral.symm 1)

/-- The constructed frame agrees on every integral differential. -/
theorem genericFrame_map (integral : KaehlerDifferential R B ≃ₗ[B] B)
    (ω : KaehlerDifferential R B) :
    genericFrame (K := K) integral (KaehlerDifferential.map R R B K ω) =
      algebraMap B K (integral ω) := lift_on_map integral ω

/-- Its dual field derivation is exactly the actual localized derivation. -/
theorem genericFrame_derivation (integral : KaehlerDifferential R B ≃ₗ[B] B) :
    frameDerivation (genericFrame (K := K) integral) = derived integral := by
  ext x
  change (derived (K := K) integral).liftKaehlerDifferential (KaehlerDifferential.D R K x) = _
  exact Derivation.liftKaehlerDifferential_comp_D _ x

end FractionKaehlerFrame318
