module
public import MayerVietorisSectionKernel318

public section
noncomputable section
namespace MayerVietorisCoefficientNaturality318
open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}} {F G : ASheaf (X:=X)}

/-- The section comparison intertwines the actual coefficient-sheaf map. -/
theorem zero_naturality (a : F ⟶ G) (U : Opens X) (x : F.H' 0 U) :
    zeroAddEquiv G U (x.comp (Ext.mk₀ a) (add_zero 0)) =
      a.hom.app (op U) (zeroAddEquiv F U x) :=
  LocalSheafCohomologySections318.zeroEquiv_naturality a U x

/-- The original terminal-generator comparison is natural in coefficients. -/
theorem terminal_naturality (a : F ⟶ G) (n : ℕ) (x : F.H' n ⊤) :
    TerminalLocalCohomology318.equivalence X G n
        (x.comp (Ext.mk₀ a) (add_zero n)) =
      Sheaf.H.map a n (TerminalLocalCohomology318.equivalence X F n x) := by
  change (Ext.mk₀ (TerminalLocalCohomology318.generatorIso X).inv).comp
      (x.comp (Ext.mk₀ a) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ (TerminalLocalCohomology318.generatorIso X).inv).comp x
      (zero_add n)).comp (Ext.mk₀ a) (add_zero n)
  simp only [Ext.comp_assoc_of_third_deg_zero]

/-- Naturality of the actual connecting map, including its terminal comparison. -/
theorem boundary_naturality (a : F ⟶ G) (U V : Opens X) (h : U ⊔ V = ⊤)
    (x : F.H' 0 (U ⊓ V)) :
    OpenMayerVietoris318.boundary G U V h
        (x.comp (Ext.mk₀ a) (add_zero 0)) =
      Sheaf.H.map a 1 (OpenMayerVietoris318.boundary F U V h x) := by
  let S := OpenMayerVietoris318.mayerVietoris U V h
  have hd : S.δ G 0 1 rfl (x.comp (Ext.mk₀ a) (add_zero 0)) =
      (S.δ F 0 1 rfl x).comp (Ext.mk₀ a) (add_zero 1) := by
    change S.shortComplex_shortExact.extClass.comp
        (x.comp (Ext.mk₀ a) (add_zero 0)) (by decide) =
      (S.shortComplex_shortExact.extClass.comp x (by decide)).comp
        (Ext.mk₀ a) (add_zero 1)
    simp only [Ext.comp_assoc_of_third_deg_zero]
  change TerminalLocalCohomology318.equivalence X G 1
      (S.δ G 0 1 rfl (x.comp (Ext.mk₀ a) (add_zero 0))) = _
  rw [hd,terminal_naturality]
  rfl

/-- Naturality on literal original sections, with the finite-minus-infinity convention unchanged. -/
theorem sectionBoundary_naturality (a : F ⟶ G) (U V : Opens X) (h : U ⊔ V = ⊤)
    (x : F.obj.obj (op (U ⊓ V))) :
    MayerVietorisSectionKernel318.sectionBoundary G U V h (a.hom.app (op (U ⊓ V)) x) =
      Sheaf.H.map a 1 (MayerVietorisSectionKernel318.sectionBoundary F U V h x) := by
  have hz : (zeroAddEquiv G (U ⊓ V)).symm (a.hom.app (op (U ⊓ V)) x) =
      ((zeroAddEquiv F (U ⊓ V)).symm x).comp (Ext.mk₀ a) (add_zero 0) := by
    apply (zeroAddEquiv G (U ⊓ V)).injective
    rw [AddEquiv.apply_symm_apply,zero_naturality,AddEquiv.apply_symm_apply]
  change OpenMayerVietoris318.boundary G U V h
      ((zeroAddEquiv G (U ⊓ V)).symm (a.hom.app (op (U ⊓ V)) x)) = _
  rw [hz,boundary_naturality]
  rfl

/-- Equality after the genuine connecting map is enough; equality of overlap sections is not required. -/
theorem cohomology_map_eq_of_boundary (U V : Opens X) (h : U ⊔ V = ⊤)
    (hsurj : Function.Surjective (MayerVietorisSectionKernel318.sectionBoundary F U V h))
    (a b : F ⟶ G)
    (hab : ∀ x, MayerVietorisSectionKernel318.sectionBoundary G U V h
      (a.hom.app (op (U ⊓ V)) x) =
      MayerVietorisSectionKernel318.sectionBoundary G U V h
      (b.hom.app (op (U ⊓ V)) x)) : Sheaf.H.map a 1 = Sheaf.H.map b 1 := by
  ext y
  obtain ⟨x,rfl⟩ := hsurj y
  simpa only [sectionBoundary_naturality] using hab x

end MayerVietorisCoefficientNaturality318
