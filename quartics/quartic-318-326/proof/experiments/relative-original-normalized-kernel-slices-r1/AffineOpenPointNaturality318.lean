module
public import AffineOpenAlgebraPoints318
public section
noncomputable section
namespace AffineOpenPointNaturality318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R A] [Algebra R S] [Algebra R T] (U : (Spec (CommRingCat.of A)).Opens)
  (φ : S →ₐ[R] T)
@[expose] def map (x : AffineOpenAlgebraPoints318.Points R A S U) :
    AffineOpenAlgebraPoints318.Points R A T U :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val,by
    simp only [Category.assoc,x.property]
    exact AffineAlgebraSchemeEquiv318.spec_over R S T φ⟩

/-- Literal scheme precomposition induces actual algebra composition,
with the base square and open embedding unchanged. -/
lemma coordinate_map (x : AffineOpenAlgebraPoints318.Points R A S U) :
    AffineOpenAlgebraPoints318.coordinate R A T U (map R A S T U φ x)=
      φ.comp (AffineOpenAlgebraPoints318.coordinate R A S U x) := by
  have hs : Spec.map (CommRingCat.ofHom
      (AffineOpenAlgebraPoints318.coordinate R A T U (map R A S T U φ x)).toRingHom)=
      Spec.map (CommRingCat.ofHom (φ.comp (AffineOpenAlgebraPoints318.coordinate R A S U x)).toRingHom) := by
    rw [AffineOpenAlgebraPoints318.coordinate_spec]
    change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val) ≫ U.ι=_
    rw [Category.assoc,←AffineOpenAlgebraPoints318.coordinate_spec]
    exact (Spec.map_comp _ _).symm
  have he := congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of T => k.hom)
    (Spec.map_injective hs)
  exact AlgHom.ext (fun a => DFunLike.congr_fun he a)
end AffineOpenPointNaturality318
