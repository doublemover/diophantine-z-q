module
public import PELOriginalGeometricFiberOrbits318
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public section
noncomputable section
namespace PELOriginalQuotientTopology318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=
  PELOriginalWholeCharacterFinite318.finite i
local instance mapSurjective (i:Fin 4):Surjective (morphism i):=
  PELOriginalWholeCharacterProper318.surjective i

/-- The actual original whole morphism is a quotient map on underlying
topological spaces, by its proved finite/closed and surjective properties. -/
theorem quotientMap (i:Fin 4):Topology.IsQuotientMap (morphism i):=
  (morphism i).isClosedMap.isQuotientMap (morphism i).continuous (morphism i).surjective

def KernelStable (i:Fin 4) (W:Set Model):Prop:=
  ∀(a:Kernel i) (p:Model),p∈W → schemeDeck a.val p∈W

/-- Original-kernel stability is enough for saturation under the ACTUAL
whole-map fibers, because scheme-point fiber/orbit identity is now proved. -/
theorem preimage_image (i:Fin 4) (W:Set Model) (hW:KernelStable i W):
    morphism i⁻¹'((morphism i)''W)=W:=by
  ext p
  constructor
  · rintro ⟨q,hq,hqp⟩
    obtain ⟨a,ha⟩:=(PELOriginalGeometricFiberOrbits318.fiber_iff_orbit i q p).mp hqp
    exact ha ▸ hW a q hq
  · intro hp
    exact ⟨p,hp,rfl⟩

lemma image_open (i:Fin 4) (W:Model.Opens) (hW:KernelStable i W):
    IsOpen ((morphism i)''(W:Set Model)):=by
  apply (quotientMap i).isCoinducing.isOpen_preimage.mp
  rw [preimage_image i W hW]
  exact W.isOpen
end PELOriginalQuotientTopology318
