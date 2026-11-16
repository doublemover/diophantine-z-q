module
public import IntegralNormalizationConductorIdeal318
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public section
noncomputable section
namespace IntegralNormalizationCounitSheaf318
open AlgebraicGeometry CategoryTheory
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "A" => Source R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "into" => IntegralFourRootNormalizationConductor318.intoNormal R a d
local notation "I" => IntegralNormalizationConductorIdeal318.ideal R a d

/-- The normalization finite dual, viewed over the literal raw order,
is isomorphic to its ACTUAL conductor ideal, not a freely chosen line. -/
@[expose] def conductorEquiv :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    FiniteDualModuleAction318.Dual P N ≃ₗ[A] I := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  let f := IntegralNormalizationCounit318.coordinate R a d
  have hr := IntegralNormalizationConductorIdeal318.range_coordinate R a d hd
  let g : FiniteDualModuleAction318.Dual P N →ₗ[A] I :=
    { toFun := fun x => ⟨f x,by rw [←hr]; exact ⟨x,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (f.map_add _ _)
      map_smul' := fun _ _ => Subtype.ext (f.map_smul _ _) }
  refine LinearEquiv.ofBijective g ⟨?_,?_⟩
  · intro x y h
    exact IntegralNormalizationCounit318.coordinate_injective R a d hd (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ LinearMap.range f := by rw [hr]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩

lemma conductorEquiv_value (f : FiniteDualModuleAction318.Dual P N) :
    (conductorEquiv R a d hd f).val=IntegralNormalizationCounit318.coordinate R a d f := rfl

/-- Genuine sheaf isomorphism on Spec of the SAME raw finite order.
This is the affine conductor description of the normalization dual;
it is not yet global duality on the proper normal or regular model. -/
@[expose] def conductorSheafIso :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    tilde (R:=CommRingCat.of A) (ModuleCat.of A (FiniteDualModuleAction318.Dual P N)) ≅
      tilde (R:=CommRingCat.of A) (ModuleCat.of A I) := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact (tilde.functor (CommRingCat.of A)).mapIso (conductorEquiv R a d hd).toModuleIso

/-- The actual sheafified normalization counit in the raw coefficient
frame. This map is not manufactured from its image after the fact. -/
@[expose] def counitSheaf :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    tilde (R:=CommRingCat.of A) (ModuleCat.of A (FiniteDualModuleAction318.Dual P N)) ⟶
      tilde (R:=CommRingCat.of A) (ModuleCat.of A A) := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  exact (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (IntegralNormalizationCounit318.coordinate R a d))

/-- The same actual map factors through the conductor subsheaf by the
produced isomorphism. This is a full sheaf-morphism equality. -/
theorem counit_factorization :
    letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
    (conductorSheafIso R a d hd).hom ≫
      (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom I.subtype)=
        counitSheaf R a d := by
  letI : Module A (FiniteDualModuleAction318.Dual P N) := Module.compHom _ into.toRingHom
  change (tilde.functor (CommRingCat.of A)).map (conductorEquiv R a d hd).toModuleIso.hom ≫
    (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom I.subtype)=_
  rw [←Functor.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact conductorEquiv_value R a d hd f
end IntegralNormalizationCounitSheaf318
