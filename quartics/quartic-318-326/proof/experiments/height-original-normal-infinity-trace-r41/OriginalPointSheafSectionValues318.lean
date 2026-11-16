module
public import OriginalGlobalPointTensorSheaf318
public import FramedPointPullbackSection318
public section
noncomputable section
namespace OriginalPointSheafSectionValues318
open NumberField OriginalPointFinitePlaceRoots318 AlgebraicGeometry CategoryTheory
open OriginalArchimedeanCotangentFiber318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i,RationalContactPoint318.parameters c t i≠0) (i : Fin 4)
local notation "T" => ContactGlobalBicanonical318.tensor c
local notation "j" => ContactIntrinsicFrames318.branchEmbedding c i
local notation "q" => ContactBranchPoint318.branchMap c t hn i
local notation "p" => RationalContactPoint318.point c t
@[expose] def localFrame : T.restrict j ≅ SheafOfModules.unit (Spec (CommRingCat.of (A c i))).ringCatSheaf :=
  IntrinsicTensorGenerator318.frame j (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
@[expose] def pointFrame : OriginalGlobalPointTensorSheaf318.pointSheaf c t ≅
    SheafOfModules.unit (Spec (CommRingCat.of (K c t))).ringCatSheaf :=
  FramedPointPullbackSection318.namedFrame q j T (localFrame c i) p
    (ContactBranchPoint318.branchMap_original c t hn i)

/-- The CANONICAL pulled section morphism on the fixed original point,
independent of any branch index or chosen trivialization. -/
@[expose] def pulledSection (s : Γ(T,⊤)) :
    SheafOfModules.unit (Spec (CommRingCat.of (K c t))).ringCatSheaf ⟶
      OriginalGlobalPointTensorSheaf318.pointSheaf c t :=
  (IdentityCotangent318.pullbackUnitIso p).inv≫
    (Scheme.Modules.pullback p).map (ModuleGlobalSections318.ofTop T s)

@[expose] def coefficient (s : Γ(T,⊤)) : A c i :=
  IntrinsicFramedTensorSections318.coefficient j (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (T.presheaf.map (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op s)

lemma restriction_formula (s : Γ(T,⊤)) :
    NormalizedSectionFrame318.framedMap j T (localFrame c i)
      (ModuleGlobalSections318.ofTop T s)=
    ClutchedModule318.multiply ((Scheme.ΓSpecIso (CommRingCat.of (A c i))).inv (coefficient c i s)) := by
  apply NormalizedSectionFrame318.framedMap_eq
  rw [ModuleTopMorphisms318.ofTop_top_one]
  change (localFrame c i).hom.app ⊤ _=
    (Scheme.ΓSpecIso (CommRingCat.of (A c i))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (A c i))).hom ((localFrame c i).hom.app ⊤ _))
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (A c i))) _).symm

/-- Every actual global section, pulled canonically at the original
WHOLE scheme point, has the exact original arithmetic branch value.
This is a full sheaf-morphism equality, not just scalar assignment. -/
theorem pulledSection_frame (s : Γ(T,⊤)) :
    pulledSection c t s≫(pointFrame c t hn i).hom=
      ClutchedModule318.multiply ((Scheme.ΓSpecIso (CommRingCat.of (K c t))).inv
        (ContactBicanonicalPointValue318.value c t hn i s)) := by
  have h := FramedPointPullbackSection318.named_section_formula q j T (localFrame c i)
    (ModuleGlobalSections318.ofTop T s)
    ((Scheme.ΓSpecIso (CommRingCat.of (A c i))).inv (coefficient c i s))
    (restriction_formula c i s) p (ContactBranchPoint318.branchMap_original c t hn i)
  change pulledSection c t s≫(pointFrame c t hn i).hom=
    ClutchedModule318.multiply (q.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (A c i))).inv (coefficient c i s))) at h
  rw [h]
  congr 1
  have hs := congrArg (fun k => k (coefficient c i s))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (ContactBranchPoint318.branchPoint c t hn i)))
  simp only [CommRingCat.comp_apply,CommRingCat.ofHom_apply] at hs
  exact hs.symm
end OriginalPointSheafSectionValues318
