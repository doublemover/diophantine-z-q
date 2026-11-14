module
public import PELOriginalQuotientTopology318
public section
noncomputable section
namespace PELOriginalInvariantMapOpenDescent318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
open PELOriginalQuotientTopology318

/-- For an invariant map to an ARBITRARY scheme, inverse images of its
opens are stable under the SAME original kernel, not just on closed points. -/
lemma inverseImage_stable {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
    (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens):
    KernelStable i (g⁻¹ᵁV):=by
  intro a p hp
  change g (schemeDeck a.val p)∈V
  have he:=congrArg (fun k:Model⟶Z=>k p) (hg a)
  change g (schemeDeck a.val p)=g p at he
  rw [he]
  exact hp

/-- Actual descended target-domain open for an arbitrary invariant
scheme map. It is a produced open, not a chosen set with assumed openness. -/
@[expose] def descendedOpen {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
    (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens):(Curve i).Opens:=
  ⟨(morphism i)''(g⁻¹ᵁV:Set Model),image_open i _ (inverseImage_stable i g hg V)⟩

/-- Exact full inverse-image equality needed to glue future local
scheme-valued factorizations. No arbitrary-target gluing is claimed yet. -/
lemma preimage_descendedOpen {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
    (hg:∀a:Kernel i,schemeDeck a.val≫g=g) (V:Z.Opens):
    morphism i⁻¹ᵁ(descendedOpen i g hg V)=g⁻¹ᵁV:=by
  apply TopologicalSpace.Opens.ext
  exact preimage_image i _ (inverseImage_stable i g hg V)

lemma descendedOpen_mono {Z:Scheme} (i:Fin 4) (g:Model⟶Z)
    (hg:∀a:Kernel i,schemeDeck a.val≫g=g) {V W:Z.Opens} (h:V≤W):
    descendedOpen i g hg V≤descendedOpen i g hg W:=
  Set.image_mono (g.preimage_mono h)
end PELOriginalInvariantMapOpenDescent318
