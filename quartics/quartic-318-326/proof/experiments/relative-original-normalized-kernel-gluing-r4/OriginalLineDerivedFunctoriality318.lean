module
public import OriginalUnitOpenFunctoriality318
public section
noncomputable section
namespace OriginalLineDerivedFunctoriality318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open NonreducedLineRestriction318 OriginalLineDerivedPullback318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line Z)

@[expose] def compositionHom :
    additive (LineSheafPullback318.line f (LineSheafPullback318.line g L)) ⟶
      additive (LineSheafPullback318.line (f ≫ g) L) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullbackComp f g).hom.app L.object)

/-- Composition of the independently constructed derived H1 maps. The
source cover is used only to detect equality via its surjective genuine
boundary; neither inverse-image cover needs to be affine. -/
lemma composition (U V : Z.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) (x : NonreducedLineMayerVietoris318.H1 L) :
    Sheaf.H.map (compositionHom f g L) 1
      (map f (LineSheafPullback318.line g L) 1 (map g L 1 x)) = map (f ≫ g) L 1 x := by
  obtain ⟨s,rfl⟩ := NonreducedLineMayerVietoris318.boundary_surjective L U V hU hV h x
  rw [boundary,boundary,boundary]
  change Sheaf.H.map (compositionHom f g L) 1
    (MayerVietorisSectionKernel318.sectionBoundary _ _ _ _ _) = _
  rw [← MayerVietorisCoefficientNaturality318.sectionBoundary_naturality]
  apply congrArg (NonreducedLineMayerVietoris318.boundary
    (LineSheafPullback318.line (f ≫ g) L) ((f ≫ g) ⁻¹ᵁ U) ((f ≫ g) ⁻¹ᵁ V)
    (InverseImageMayerVietoris318.inverseImage_cover (f ≫ g).base U V h))
  exact OriginalUnitOpenFunctoriality318.composition f g L.object (U ⊓ V) s

variable (L₀ : Line X)
@[expose] def identityHom : additive (LineSheafPullback318.line (𝟙 X) L₀) ⟶ additive L₀ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullbackId X).hom.app L₀.object)

lemma identity (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤) (x : NonreducedLineMayerVietoris318.H1 L₀) :
    Sheaf.H.map (identityHom L₀) 1 (map (𝟙 X) L₀ 1 x) = x := by
  obtain ⟨s,rfl⟩ := NonreducedLineMayerVietoris318.boundary_surjective L₀ U V hU hV h x
  rw [boundary]
  change Sheaf.H.map (identityHom L₀) 1
    (MayerVietorisSectionKernel318.sectionBoundary _ _ _ _ _) = _
  rw [← MayerVietorisCoefficientNaturality318.sectionBoundary_naturality]
  apply congrArg (NonreducedLineMayerVietoris318.boundary L₀ U V h)
  exact OriginalUnitOpenFunctoriality318.identity L₀.object (U ⊓ V) s

/-- Equality of the actual geometric maps carries the genuine pullback
comparison, rather than identifying their cohomology carriers silently. -/
lemma congr {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (N : Line Y) (n : ℕ)
    (x : Sheaf.H (additive N) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((Scheme.Modules.pullbackCongr h).hom.app N.object)) n (map f₁ N n x) = map f₂ N n x := by
  cases h
  simp only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app,
    Functor.map_id,Sheaf.H.map_id_apply]
end OriginalLineDerivedFunctoriality318
