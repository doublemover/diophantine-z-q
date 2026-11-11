module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.Length
public section
noncomputable section
namespace CanonicalStalkModule318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} {M N : X.Modules}
/-- The actual additive sheaf stalk, with the canonical local-ring action
constructed by the presheaf-of-modules filtered colimit. -/
@[expose] abbrev stalk (M : X.Modules) (x : X) : Type u := M.presheaf.stalk x
instance (M : X.Modules) (x : X) : Module (X.presheaf.stalk x) (stalk M x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk M.val.presheaf x))
/-- Linearity of the ACTUAL induced stalk map. Both scalar and module
germs are restricted to the same neighborhood before using section linearity. -/
lemma map_smul (f : M ⟶ N) (x : X) (r : X.presheaf.stalk x) (m : stalk M x) :
    (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf (r • m) =
      r • (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf m := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, s, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a,
    ← PresheafOfModules.germ_smul M.val x V hxV]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change N.presheaf.germ V x hxV (f.app V (_ • s)) = _
  rw [Scheme.Modules.Hom.app_smul, PresheafOfModules.germ_smul N.val]
/-- No new action is transported through this map: it uses the existing
canonical local-ring actions on both actual additive stalks. -/
def map (f : M ⟶ N) (x : X) : stalk M x →ₗ[X.presheaf.stalk x] stalk N x where
  __ := ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf).hom
  map_smul' := map_smul f x
/-- A sheaf isomorphism induces an isomorphism of the genuine stalk modules. -/
def iso (e : M ≅ N) (x : X) : stalk M x ≃ₗ[X.presheaf.stalk x] stalk N x where
  __ := ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab x).mapIso e).addCommGroupIsoToAddEquiv
  map_smul' := map_smul e.hom x
lemma length_iso (e : M ≅ N) (x : X) :
    Module.length (X.presheaf.stalk x) (stalk M x) =
      Module.length (X.presheaf.stalk x) (stalk N x) := (iso e x).length_eq
/-- Length is unchanged by an actual semilinear bijection over a ring
isomorphism, via the FULL lattice of submodules. -/
lemma length_semilinear {R S A B : Type*} [CommRing R] [CommRing S]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module S B]
    (σ : R ≃+* S) (e : A ≃ₛₗ[σ.toRingHom] B) :
    Module.length R A = Module.length S B := by
  letI : RingHomSurjective σ.toRingHom := ⟨σ.surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective e.toLinearMap e.bijective)]
end CanonicalStalkModule318
