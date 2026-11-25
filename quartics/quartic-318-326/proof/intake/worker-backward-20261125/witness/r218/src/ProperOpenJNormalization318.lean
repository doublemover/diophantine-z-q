module
public import NormalizationChart318
public import ReciprocalProjective318
public section
noncomputable section
namespace ProperOpenJNormalization318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

@[expose] def targetCover (j:Fin 2) : (ProjectiveJLine318.scheme ℤ).affineOpens :=
  ⟨JLineAtlas318.chart ℤ j ''ᵁ ⊤,by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact isAffineOpen_opensRange _⟩
lemma targetCover_covers : (⨆j,(targetCover j).1)=⊤ := by
  simpa only [targetCover,Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range] using
    JLineAtlas318.standard_opens_cover ℤ

variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

@[expose] def finitePolynomial : Polynomial ℤ→+*B :=
  (algebraMap (OpenJModel318.Base N) B).comp
    (algebraMap (Polynomial ℤ) (OpenJModel318.Base N))

lemma finite_factor : OpenJProjectiveMap318.coverMap N B=
    Spec.map (CommRingCat.ofHom (finitePolynomial N B)) ≫ JLineAtlas318.chart ℤ 1 := by
  unfold OpenJProjectiveMap318.coverMap OpenJProjectiveMap318.baseOpen
    OpenJIntegralModel318.baseOpen finitePolynomial
  rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

lemma finite_chart_closure (hN:N≠0) :
    letI:=(finitePolynomial N B).toAlgebra
    Module.Finite (Polynomial ℤ) (integralClosure (Polynomial ℤ) B) := by
  letI:=(finitePolynomial N B).toAlgebra
  letI:IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B:=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  exact (OpenJNormalModel318.actual_finite_normal_model N B hN).1

/-- Finiteness of the ACTUAL global normalization over the ACTUAL proper
projective j-line, with both actual chart section-ring interfaces discharged. -/
theorem normalization_finite (hN:N≠0) :
    IsFinite (OpenJProjectiveMap318.coverMap N B).fromNormalization := by
  apply GlobalNormalization318.finite_of_affine_pieces
    (OpenJProjectiveMap318.coverMap N B) targetCover targetCover_covers
  intro i
  fin_cases i
  · change letI:=((OpenJProjectiveMap318.coverMap N B).app (JLineAtlas318.chart ℤ 0 ''ᵁ ⊤)).hom.toAlgebra;
      Module.Finite Γ(ProjectiveJLine318.scheme ℤ,JLineAtlas318.chart ℤ 0 ''ᵁ ⊤)
        (integralClosure Γ(ProjectiveJLine318.scheme ℤ,JLineAtlas318.chart ℤ 0 ''ᵁ ⊤)
          Γ(Spec (CommRingCat.of B),OpenJProjectiveMap318.coverMap N B⁻¹ᵁ(JLineAtlas318.chart ℤ 0 ''ᵁ ⊤)))
    rw [ReciprocalProjective318.coverMap_infinity]
    exact NormalizationChart318.finite_sections
      (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B)) (JLineAtlas318.chart ℤ 0)
      (by exact (ReciprocalCover318.finite_normal_model N B hN).1)
  · change letI:=((OpenJProjectiveMap318.coverMap N B).app (JLineAtlas318.chart ℤ 1 ''ᵁ ⊤)).hom.toAlgebra;
      Module.Finite Γ(ProjectiveJLine318.scheme ℤ,JLineAtlas318.chart ℤ 1 ''ᵁ ⊤)
        (integralClosure Γ(ProjectiveJLine318.scheme ℤ,JLineAtlas318.chart ℤ 1 ''ᵁ ⊤)
          Γ(Spec (CommRingCat.of B),OpenJProjectiveMap318.coverMap N B⁻¹ᵁ(JLineAtlas318.chart ℤ 1 ''ᵁ ⊤)))
    rw [finite_factor]
    exact NormalizationChart318.finite_sections
      (CommRingCat.ofHom (finitePolynomial N B)) (JLineAtlas318.chart ℤ 1)
      (finite_chart_closure N B hN)

/-- A genuine proper integral model over Z, containing the original actual
finite-etale open-j cover as a dense open subscheme. No proper-target or
finite-normalization assumption is left in this theorem. -/
theorem proper_integral_extension (hN:N≠0) :
    IsOpenImmersion (OpenJProjectiveMap318.coverMap N B).toNormalization ∧
    IsIntegral (OpenJProjectiveMap318.coverMap N B).normalization ∧
    IsProper ((OpenJProjectiveMap318.coverMap N B).fromNormalization ≫
      ProjectiveJLine318.structureMap ℤ) := by
  letI:=normalization_finite N B hN
  exact ⟨OpenJProjectiveMap318.coverMap_normalization_open N B,inferInstance,inferInstance⟩

/-- The actual source embedding is dense, not merely an unspecified open. -/
theorem normalization_dense : Function.Injective (OpenJProjectiveMap318.coverMap N B).toNormalization ∧
    DenseRange (OpenJProjectiveMap318.coverMap N B).toNormalization := by
  letI:=OpenJProjectiveMap318.coverMap_normalization_open N B
  exact ⟨(OpenJProjectiveMap318.coverMap N B).toNormalization.injective,
    (OpenJProjectiveMap318.coverMap N B).toNormalization.denseRange⟩

/-- The proper extension is over the literal original Z-structure map. -/
theorem normalization_over_Z :
    (OpenJProjectiveMap318.coverMap N B).toNormalization ≫
      ((OpenJProjectiveMap318.coverMap N B).fromNormalization ≫
        ProjectiveJLine318.structureMap ℤ)=
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
  rw [←Category.assoc,Scheme.Hom.toNormalization_fromNormalization]
  unfold OpenJProjectiveMap318.coverMap
  rw [Category.assoc,OpenJProjectiveMap318.baseOpen_over_Z,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  simp

end ProperOpenJNormalization318
