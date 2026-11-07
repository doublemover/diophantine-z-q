module
public import PointedArithmeticModel318
public import OrbitQuotientScheme318
public section
noncomputable section
namespace PointedQuotientModel318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open InvariantBaseChange318 EtaleInvariantQuotient318 PointedArithmeticModel318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N:ℕ) (B S Ω G X:Type)
  [CommRing B] [CommRing S] [Field Ω]
  [Algebra (OpenJModel318.Base N) B] [Algebra (OpenJModel318.Base N) S]
  [Module.FaithfullyFlat (OpenJModel318.Base N) S]
  [Group G] [Finite G] [MulAction G X] [Finite X]
  (ρ:G→B≃ₐ[OpenJModel318.Base N]B)
  (e:S⊗[OpenJModel318.Base N]B≃ₐ[S](X→S))
  (he:∀ (g:G) (b:S⊗[OpenJModel318.Base N]B) (x:X),
    e (baseAction S ρ g b) x=e b (g•x))

@[expose] def quotientPoint (β:B→+*Ω) : invariants ρ→+*Ω :=
  β.comp (invariants ρ).val.toRingHom

/-- An actual field-valued original-cover point selects a component of the
actual invariant quotient. Neither quotient etaleness nor a domain component
is a supplied premise. The source equivariant split remains explicit. -/
@[expose] def component (hN:N≠0) (β:B→+*Ω) :
    PointedComponent N (invariants ρ) Ω (quotientPoint N B Ω G ρ β) := by
  obtain ⟨hf,het⟩:=finite_etale_of_faithfullyFlat_split S ρ e he
  letI:=hf
  letI:=het
  exact ofPoint N (invariants ρ) Ω hN (quotientPoint N B Ω G ρ β)

variable {N B S Ω G X}

/-- The exact original-cover point maps to its restricted quotient point. -/
theorem quotient_point_factor (β:B→+*Ω) :
    Spec.map (CommRingCat.ofHom (quotientPoint N B Ω G ρ β))=
      Spec.map (CommRingCat.ofHom β) ≫ OrbitQuotientScheme318.quotientMap ρ := by
  unfold OrbitQuotientScheme318.quotientMap
  rw [←Spec.map_comp]
  rfl

/-- The selected component contains precisely that quotient image, with
actual Scheme morphisms rather than a cardinality or nonemptiness argument. -/
theorem selected_point_factor (hN:N≠0) (β:B→+*Ω) :
    let c:=component N B S Ω G X ρ e he hN β
    Spec.map (CommRingCat.ofHom (lift c)) ≫ inclusion c=
      Spec.map (CommRingCat.ofHom β) ≫ OrbitQuotientScheme318.quotientMap ρ := by
  dsimp only
  rw [original_point_factor]
  exact quotient_point_factor ρ β

/-- Properness, flatness, surjectivity and normality all concern the same
actual component model built from the quotient and the given point. -/
theorem constructed_model_properties (hN:N≠0) (β:B→+*Ω) :
    let c:=component N B S Ω G X ρ e he hN β
    IsIntegral (model c) ∧ AlgebraicGeometry.IsNoetherian (model c) ∧
    IsProper (structureMap c) ∧ Flat (structureMap c) ∧ Surjective (structureMap c) ∧
    (∀x:model c,IsIntegrallyClosed ((model c).presheaf.stalk x)) ∧
    (∀j:Fin 2,ringKrullDim (NormalJModel318.chartRing N (Ring c) j)=2) := by
  dsimp only
  let c:=component N B S Ω G X ρ e he hN β
  obtain ⟨hp,hf,hs⟩:=proper_flat_surjective c hN
  exact ⟨model_integral c,model_noetherian c hN,hp,hf,hs,
    model_normal_stalk c hN,chart_dimension_two c hN⟩

/-- The given point survives all the way to the proper arithmetic model,
with its exact original base morphism. -/
theorem constructed_point_over_Z (hN:N≠0) (β:B→+*Ω) :
    let c:=component N B S Ω G X ρ e he hN β
    point c ≫ structureMap c=Spec.map (CommRingCat.ofHom (Int.castRingHom Ω)) :=
  point_over_Z _

end PointedQuotientModel318
