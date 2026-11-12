module
public import TwoOpenGlobalSectionsFlatComparison318
public section
noncomputable section
namespace TwoOpenNamedCoefficientComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {U V X N : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b]
variable (l : N ⟶ U) (r : N ⟶ V) (H : IsPullback l r a b)
open TwoOpenSourceUnion318
variable {R : Type u} [CommRing R] (base : R →+* Γ(scheme a b,⊤))
variable (A : Type u) [CommRing A] [Algebra R A] [Module.Flat R A]
/-- Install the exact coefficient actions from the NAMED whole base
map. No hidden-map algebra instance is registered, and no local
section action or commutative square is assumed. -/
def comparison := by
  letI : Algebra R Γ(scheme a b,⊤) := base.toAlgebra
  letI : Algebra R Γ(U,⊤) := ((left a b).appTop.hom.comp base).toAlgebra
  letI : Algebra R Γ(V,⊤) := ((right a b).appTop.hom.comp base).toAlgebra
  letI : Algebra R Γ(N,⊤) :=
    ((l.appTop.hom.comp (left a b).appTop.hom).comp base).toAlgebra
  let s : Γ(scheme a b,⊤) →ₐ[R] Γ(U,⊤) :=
    { (left a b).appTop.hom with commutes' := fun _ => rfl }
  let t : Γ(scheme a b,⊤) →ₐ[R] Γ(V,⊤) :=
    { (right a b).appTop.hom with commutes' := fun _ => rfl }
  let f : Γ(U,⊤) →ₐ[R] Γ(N,⊤) :=
    { l.appTop.hom with commutes' := fun _ => rfl }
  have hsquare : l≫left a b=r≫right a b := by
    apply (cancel_mono (opens a b).ι).mp
    simpa only [Category.assoc,left_into,right_into] using H.w
  let g : Γ(V,⊤) →ₐ[R] Γ(N,⊤) :=
    { r.appTop.hom with commutes' := fun z => by
        change r.appTop.hom ((right a b).appTop.hom (base z))=
          l.appTop.hom ((left a b).appTop.hom (base z))
        have hh := congrArg (fun k : N ⟶ scheme a b => k.appTop.hom (base z)) hsquare.symm
        simpa only [Scheme.Hom.comp_appTop] using hh }
  exact TwoOpenGlobalSectionsFlatComparison318.equivalence a b l r H s t f g rfl rfl rfl rfl A
lemma pure_value :
    letI : Algebra R Γ(scheme a b,⊤) := base.toAlgebra
    letI : Algebra R Γ(U,⊤) := ((left a b).appTop.hom.comp base).toAlgebra
    letI : Algebra R Γ(V,⊤) := ((right a b).appTop.hom.comp base).toAlgebra
    ∀ (c : A) (z : Γ(scheme a b,⊤)),
      (comparison a b l r H base A (c ⊗ₜ[R] z)).val=
        (c ⊗ₜ[R] (left a b).appTop.hom z,c ⊗ₜ[R] (right a b).appTop.hom z) := by
  letI : Algebra R Γ(scheme a b,⊤) := base.toAlgebra
  letI : Algebra R Γ(U,⊤) := ((left a b).appTop.hom.comp base).toAlgebra
  letI : Algebra R Γ(V,⊤) := ((right a b).appTop.hom.comp base).toAlgebra
  intro c z
  rfl
end TwoOpenNamedCoefficientComparison318
