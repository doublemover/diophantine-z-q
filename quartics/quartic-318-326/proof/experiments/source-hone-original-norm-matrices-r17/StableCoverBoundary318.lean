module
public import SchemeBoundaryNaturality318
public import AffineChartPullbackScalars318
public import AffineChartRingSections318

public section
noncomputable section
namespace StableCoverBoundary318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MayerVietorisSectionKernel318 LocalSheafCohomologySections318
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Changing only proved-equal opens uses their actual section transport. -/
theorem boundary_congr {X : TopCat.{0}} (F : ASheaf (X:=X))
    (U V U' V' : Opens X) (h : U ⊔ V = ⊤) (h' : U' ⊔ V' = ⊤)
    (hU : U' = U) (hV : V' = V) (x : F.obj.obj (op (U' ⊓ V'))) :
    sectionBoundary F U' V' h' x = sectionBoundary F U V h
      (F.obj.map (homOfLE (show U ⊓ V ≤ U' ⊓ V' by rw [hU,hV])).op x) := by
  subst U'
  subst V'
  change sectionBoundary F U V h' x = sectionBoundary F U V h
    (F.obj.map (𝟙 (op (U ⊓ V))) x)
  rw [F.obj.map_id]
  rfl

/-- A cover-preserving original scheme map acts by its literal section map on the same cover. -/
theorem pullback_stable_boundary {X : Scheme.{0}} (f : X ⟶ X)
    (U V : X.Opens) (h : U ⊔ V = ⊤) (hU : f ⁻¹ᵁ U = U) (hV : f ⁻¹ᵁ V = V)
    (x : Γ(X,U ⊓ V)) :
    SchemeSourceCohomology318.pullback f 1
      (sectionBoundary (StructureAdditiveSheaf318.sheaf X) U V h x) =
    sectionBoundary (StructureAdditiveSheaf318.sheaf X) U V h
      (f.appLE (U ⊓ V) (U ⊓ V)
        (show U ⊓ V ≤ f ⁻¹ᵁ (U ⊓ V) by rw [Scheme.Hom.preimage_inf,hU,hV]) x) := by
  rw [SchemeBoundaryNaturality318.scheme_pullback_sectionBoundary]
  exact boundary_congr (StructureAdditiveSheaf318.sheaf X) U V
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) h
    (InverseImageMayerVietoris318.inverseImage_cover f.base U V h) hU hV (f.app (U ⊓ V) x)

/-- Literal affine coordinates intertwine any actual commuting chart square. -/
theorem affine_coordinates {X : Scheme.{0}} {A : Type} [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ X) (a : A →+* A) (hsq : j ≫ f = Spec.map (CommRingCat.ofHom a) ≫ j)
    (U : X.Opens) (hU : j ''ᵁ ⊤ = U) (hstable : f ⁻¹ᵁ U = U) (x : A) :
    f.appLE U U (le_of_eq hstable.symm)
      (AffineChartRingSections318.equivalenceOn j U hU x) =
    AffineChartRingSections318.equivalenceOn j U hU (a x) := by
  subst U
  exact AffineChartPullbackScalars318.affine_scalar (CommRingCat.ofHom a) f j j hsq
    (le_of_eq hstable.symm) x

end StableCoverBoundary318
