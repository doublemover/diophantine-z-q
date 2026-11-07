module
public import PointedQuotientModel318
public import PrimitiveDiamond318
public section
noncomputable section
namespace PrimitivePointedModel318
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open InvariantBaseChange318 PointedArithmeticModel318 PrimitiveDiamond318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

variable (N:ℕ) [NeZero N] (B S Ω:Type)
  [CommRing B] [CommRing S] [Field Ω]
  [Algebra (OpenJModel318.Base N) B] [Algebra (OpenJModel318.Base N) S]
  [Module.FaithfullyFlat (OpenJModel318.Base N) S]
  (H:Subgroup (ZMod N)ˣ) (ρ:H→B≃ₐ[OpenJModel318.Base N]B)
  (e:S⊗[OpenJModel318.Base N]B≃ₐ[S](Points N→S))
  (he:∀ (g:H) (b:S⊗[OpenJModel318.Base N]B) (x:Points N),
    e (baseAction S ρ g b) x=e b (g•x))

/-- The component uses the existing exact-order primitive pair predicate
and the actual diamond subgroup action, with no substitute point labels. -/
@[expose] def component (β:B→+*Ω) :
    PointedComponent N (invariants ρ) Ω
      (PointedQuotientModel318.quotientPoint N B Ω H ρ β) :=
  PointedQuotientModel318.component N B S Ω H (Points N) ρ e he (NeZero.ne N) β

/-- The primitive-marking canonical torsor and the pointed proper arithmetic
model are constructed from the very same algebra and equivariant splitting.
Freeness and quotient finite-etaleness are proved upstream, not assumed here. -/
theorem torsor_and_model (β:B→+*Ω) :
    Nonempty (B⊗[invariants ρ]B≃ₐ[invariants ρ](H→B)) ∧
    let c:=component N B S Ω H ρ e he β
    IsIntegral (model c) ∧ AlgebraicGeometry.IsNoetherian (model c) ∧
    IsProper (structureMap c) ∧ Flat (structureMap c) ∧ Surjective (structureMap c) ∧
    (∀x:model c,IsIntegrallyClosed ((model c).presheaf.stalk x)) ∧
    (∀j:Fin 2,ringKrullDim (NormalJModel318.chartRing N (Ring c) j)=2) := by
  refine ⟨⟨primitiveTorsorEquiv N S H ρ e he⟩,?_⟩
  exact PointedQuotientModel318.constructed_model_properties ρ e he (NeZero.ne N) β

/-- The torsor is the canonical action tensor map, not an arbitrary
isomorphism of equal-rank modules. -/
theorem torsor_formula (b c:B) (g:H) :
    primitiveTorsorEquiv N S H ρ e he (b⊗ₜ[invariants ρ]c) g=b*ρ g c :=
  primitiveTorsorEquiv_tmul N S H ρ e he b c g

/-- The original marked point maps to the chosen quotient component. -/
theorem original_point_factor (β:B→+*Ω) :
    let c:=component N B S Ω H ρ e he β
    Spec.map (CommRingCat.ofHom (lift c)) ≫ inclusion c=
      Spec.map (CommRingCat.ofHom β) ≫ OrbitQuotientScheme318.quotientMap ρ :=
  PointedQuotientModel318.selected_point_factor ρ e he (NeZero.ne N) β

/-- That exact point reaches the constructed proper model over Spec Z. -/
theorem point_over_Z (β:B→+*Ω) :
    let c:=component N B S Ω H ρ e he β
    point c ≫ structureMap c=Spec.map (CommRingCat.ofHom (Int.castRingHom Ω)) :=
  PointedQuotientModel318.constructed_point_over_Z ρ e he (NeZero.ne N) β

end PrimitivePointedModel318
