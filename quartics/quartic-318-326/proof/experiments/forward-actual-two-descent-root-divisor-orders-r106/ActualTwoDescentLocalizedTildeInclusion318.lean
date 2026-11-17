module
public import ActualTwoDescentLocalizedInclusionIsomorphism318
public section
noncomputable section
namespace ActualTwoDescentLocalizedTildeInclusion318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentLocalizedInclusionIsomorphism318
universe u

/-- Transport invertibility of an exact map across a natural isomorphism. -/
lemma map_isIso_of_natIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (f : X ⟶ Y) [IsIso (G.map f)] :
    IsIso (F.map f) := by
  have h : F.map f=e.hom.app X ≫ G.map f ≫ e.inv.app Y := by
    rw [←Category.assoc,←e.hom.naturality f]
    simp
  rw [h]
  infer_instance

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]

include M in
/-- Native tilde restriction consumes the SAME ideal inclusion, using
naturality of the actual scalar-extension comparison. -/
lemma actual_tilde_inclusion_isIso (I : Ideal R) (hI : I.map (algebraMap R S)=⊤) :
    IsIso ((Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
      ((tilde.functor (CommRingCat.of R)).map (ModuleCat.ofHom I.subtype))) := by
  letI := actual_extended_inclusion_isIso (S:=S) M I hI
  exact map_isIso_of_natIso
    (TildePullback318.restrictionIso (CommRingCat.ofHom (algebraMap R S)))
    (ModuleCat.ofHom I.subtype)
end ActualTwoDescentLocalizedTildeInclusion318
