module
public import PELOriginalAffineFiberOrbits318
public section
noncomputable section
namespace PELOriginalGeometricFiberOrbits318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalKernelStableOpens318 PELOriginalSectionKernelAction318
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2

/-- EVERY actual scheme-point fiber, including generic points and all
infinity points, is a single orbit of the same original character kernel. -/
theorem fiber_iff_orbit (i:Fin 4) (p q:Model):
    morphism i p=morphism i q ↔ ∃a:Kernel i,schemeDeck a.val p=q:=by
  constructor
  · intro he
    obtain ⟨U,_,hp,hU,_⟩:=PELOriginalCharacterNormalBasis318.hasBasis i ⊤
      ⟨morphism i p,by trivial⟩
    have hq:morphism i q∈U:=he ▸ hp
    exact PELOriginalAffineFiberOrbits318.affine_fiber_orbit i U hU p q hp hq he
  · rintro ⟨a,rfl⟩
    exact (congrArg (fun k:Model⟶Curve i=>k p)
      (PELOriginalWholeCharacterDeck318.whole_deck_square i a.val a.property)).symm
end PELOriginalGeometricFiberOrbits318
