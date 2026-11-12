module
public import DifferentialFunctor318
public section
noncomputable section
namespace GlobalDifferentialFunctor318
open AlgebraicGeometry CategoryTheory KaehlerDifferential
open CanonicalDifferentialSheafMap318 AffineDifferentialSheaf318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- Transport of genuine global sections via the canonical actual sheaf morphism
and actual affine pushforward global-section comparison. -/
@[expose] def map (f : S →ₐ[R] T) : GlobalDifferentials (R:=R) (S:=S) →
    GlobalDifferentials (R:=R) (S:=T) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact fun s => (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap S T))
    (targetSheaf (R:=R) (T:=T))).hom
      ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=S) (T:=T))) s)

theorem map_section (f : S →ₐ[R] T) (ω : KaehlerDifferential R S) :
    map f ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω)=
      (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom
        (AlgHomDifferential318.map f ω) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact global_image ω

/-- Exact composition on all genuine affine differential global sections. -/
theorem map_comp_apply (f : S →ₐ[R] T) (g : T →ₐ[R] U)
    (s : GlobalDifferentials (R:=R) (S:=S)) : map (g.comp f) s=map g (map f s) := by
  let e:=tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))
  obtain ⟨ω,rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 s
  rw [map_section,map_section,map_section,DifferentialFunctor318.map_comp_apply]

theorem map_id_apply (s : GlobalDifferentials (R:=R) (S:=S)) : map (AlgHom.id R S) s=s := by
  let e:=tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))
  obtain ⟨ω,rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 s
  rw [map_section,DifferentialFunctor318.map_id_apply]

/-- Every actual commutative algebra-map square gives path-independent sheaf section transport. -/
theorem square {V : Type u} [CommRing V] [Algebra R V]
    (f : S →ₐ[R] T) (g : S →ₐ[R] U) (h : T →ₐ[R] V) (k : U →ₐ[R] V)
    (heq : h.comp f=k.comp g) (s : GlobalDifferentials (R:=R) (S:=S)) :
    map h (map f s)=map k (map g s) := by
  rw [←map_comp_apply,←map_comp_apply,heq]
end GlobalDifferentialFunctor318
