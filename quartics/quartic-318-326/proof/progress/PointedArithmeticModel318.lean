module
public import ComponentPointFactor318
public import JModelDimension318
public import JModelGenericTensor318
public section
noncomputable section
namespace PointedArithmeticModel318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N:ℕ) (B Ω:Type) [CommRing B] [Field Ω]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

/-- An actual chosen component together with the field-valued point it contains.
The finite-etale and domain structures are constructed by `ofPoint` below. -/
structure PointedComponent (β:B→+*Ω) where
  idempotent : B
  idempotent_spec : IsIdempotentElem idempotent
  point_spec : β idempotent=1
  domain : IsDomain (Localization.Away idempotent)
  finite : Module.Finite (OpenJModel318.Base N) (Localization.Away idempotent)
  etale : Algebra.Etale (OpenJModel318.Base N) (Localization.Away idempotent)

@[expose] def ofPoint (hN:N≠0) (β:B→+*Ω) : PointedComponent N B Ω β := by
  have h:=PointedOpenJ318.exists_component N B Ω hN β
  let e:=Classical.choose h
  have he:=Classical.choose_spec h
  exact ⟨e,he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩

variable {N B Ω} {β:B→+*Ω} (c:PointedComponent N B Ω β)
omit [Module.Finite (OpenJModel318.Base N) B] [Algebra.Etale (OpenJModel318.Base N) B]

abbrev Ring := Localization.Away c.idempotent
attribute [instance] PointedComponent.domain PointedComponent.finite PointedComponent.etale

@[expose] def inclusion : Spec (CommRingCat.of (Ring c)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Ring c)))

@[expose] def lift : Ring c→+*Ω :=
  ComponentPointFactor318.pointLift β c.idempotent c.point_spec

abbrev model : Scheme := (OpenJProjectiveMap318.coverMap N (Ring c)).normalization

@[expose] def sourceMap : Spec (CommRingCat.of (Ring c)) ⟶ model c :=
  (OpenJProjectiveMap318.coverMap N (Ring c)).toNormalization

@[expose] def structureMap : model c ⟶ Spec (CommRingCat.of ℤ) :=
  ArithmeticJModel318.structureMap N (Ring c)

@[expose] def point : Spec (CommRingCat.of Ω) ⟶ model c :=
  Spec.map (CommRingCat.ofHom (lift c)) ≫ sourceMap c

/-- The point is the original point, not an independently selected point of
an arbitrary nonempty component. -/
theorem original_point_factor :
    Spec.map (CommRingCat.ofHom (lift c)) ≫ inclusion c=
      Spec.map (CommRingCat.ofHom β) :=
  ComponentPointFactor318.scheme_point_factor β c.idempotent c.point_spec

theorem inclusion_open_closed : IsOpenImmersion (inclusion c) ∧
    IsClosedImmersion (inclusion c) :=
  by
    let : Nontrivial B := RingHom.domain_nontrivial β
    exact OpenJComponent318.component_open_closed B c.idempotent c.idempotent_spec

theorem source_open : IsOpenImmersion (sourceMap c) :=
  OpenJProjectiveMap318.coverMap_normalization_open N (Ring c)

theorem model_integral : IsIntegral (model c) := inferInstance

theorem proper_flat_surjective (hN:N≠0) :
    IsProper (structureMap c) ∧ Flat (structureMap c) ∧ Surjective (structureMap c) :=
  ArithmeticJModel318.proper_flat_surjective N (Ring c) hN

theorem model_noetherian (hN:N≠0) : AlgebraicGeometry.IsNoetherian (model c) :=
  NormalJModel318.noetherian_model N (Ring c) hN

theorem model_normal_stalk (hN:N≠0) (x:model c) :
    IsIntegrallyClosed ((model c).presheaf.stalk x) :=
  NormalJModel318.normal_stalk N (Ring c) hN x

theorem chart_dimension_two (hN:N≠0) (j:Fin 2) :
    ringKrullDim (NormalJModel318.chartRing N (Ring c) j)=2 :=
  JModelDimension318.chart_dimension_two N (Ring c) hN j

/-- Exact compatibility with the original point's arithmetic base map. -/
theorem point_over_Z : point c ≫ structureMap c=
    Spec.map (CommRingCat.ofHom (Int.castRingHom Ω)) := by
  unfold point sourceMap structureMap ArithmeticJModel318.structureMap
  rw [Category.assoc,ProperOpenJNormalization318.normalization_over_Z]
  rw [←Spec.map_comp]
  congr 1
  ext z
  simp

attribute [local instance] JModelFunctionField318.sourceAlgebra

/-- The point-selected model has the actual generic field of this same
component, with its original coefficient map preserved. -/
@[expose] def genericEquiv (hN:N≠0) :
    (model c).functionField ≃ₐ[Ring c]
      JModelGenericTensor318.Generic N (Ring c) :=
  JModelGenericTensor318.genericEquiv N (Ring c) hN

theorem genericEquiv_coeff (hN:N≠0) (b:Ring c) :
    genericEquiv c hN (algebraMap (Ring c) (model c).functionField b)=
      algebraMap (Ring c) (JModelGenericTensor318.Generic N (Ring c)) b :=
  (genericEquiv c hN).commutes b

end PointedArithmeticModel318
