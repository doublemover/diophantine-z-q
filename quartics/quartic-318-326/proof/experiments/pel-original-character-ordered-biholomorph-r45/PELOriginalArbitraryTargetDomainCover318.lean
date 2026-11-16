module
public import PELOriginalLocalSchemeFactorization318
public import FlatSurjectiveLocalFactorAgreement318
public import PELOriginalWholeCharacterFlat318
public section
noncomputable section
namespace PELOriginalArbitraryTargetDomainCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalInvariantMapOpenDescent318
variable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
  (hg:∀a:Kernel i,schemeDeck a.val≫g=g)
local instance mapSurjective:Surjective (morphism i):=PELOriginalWholeCharacterProper318.surjective i

@[expose] def domain (V:Z.affineOpens):(Curve i).Opens:=descendedOpen i g hg V.val

/-- All affine opens of the ORIGINAL arbitrary target yield a cover of
the produced descended domains, by actual whole-map surjectivity. -/
lemma domain_cover:IsOpenCover (domain i g hg):=by
  apply le_antisymm le_top
  intro y _
  obtain ⟨p,hp⟩:=(morphism i).surjective y
  obtain ⟨V,hV,hpV,_⟩:=exists_isAffineOpen_mem_and_subset
    (show g p∈(⊤:Z.Opens) from trivial)
  exact Opens.mem_iSup.mpr ⟨⟨V,hV⟩,⟨p,hpV,hp⟩⟩

@[expose] def cover:(Curve i).OpenCover:=
  Scheme.openCoverOfIsOpenCover (Curve i) (domain i g hg) (domain_cover i g hg)

lemma source_cover:IsOpenCover (fun V:Z.affineOpens=>morphism i⁻¹ᵁdomain i g hg V):=by
  rw [←Scheme.Hom.preimage_iSup,domain_cover,Scheme.Hom.preimage_top]

@[expose] def sourceCover:Model.OpenCover:=
  Scheme.openCoverOfIsOpenCover Model (fun V:Z.affineOpens=>morphism i⁻¹ᵁdomain i g hg V)
    (source_cover i g hg)
end PELOriginalArbitraryTargetDomainCover318
