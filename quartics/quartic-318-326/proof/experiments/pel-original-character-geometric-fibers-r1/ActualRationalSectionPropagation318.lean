module
public import ActualLineRationalEquations318
public section
noncomputable section
namespace ActualRationalSectionPropagation318
open AlgebraicGeometry CategoryTheory
universe u
variable {X:Scheme.{u}} [IsIntegral X] (M:X.Modules) {ι:Type u}
    (U:ι→X.Opens) [∀i,Nonempty (U i)]
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
lemma restrict_chain {A B C:X.Opens}(hAB:A≤B)(hBC:B≤C)(s:Γ(M,C)):
    M.presheaf.map (homOfLE hAB).op (M.presheaf.map (homOfLE hBC).op s)=
      M.presheaf.map (homOfLE (hAB.trans hBC)).op s:=
  (Functor.map_comp_apply M.presheaf (homOfLE hBC).op (homOfLE hAB).op s).symm
variable (reference:ι)(f₀:X.functionField)
/-- If the original anchor is the restriction of a genuine section on
one larger actual open, the rational equations equal its actual frame
coefficients on EVERY subopen there, not only on the reference overlap.
Nonempty intersection and genuine generic germ restriction propagate
the identity without extending a regular section across a pole. -/
theorem from_larger_open(V:X.Opens)(href:U reference≤V)(s:Γ(M,V))
    (hanchor:X.germToFunctionField (U reference)
      ((OpenLineFrameCoordinates318.frame M (U reference) (frames reference)
        (U reference) le_rfl).symm
        (M.presheaf.map (homOfLE href).op s))=f₀)
    (i:ι)(W:X.Opens)[Nonempty W](hi:W≤U i)(hV:W≤V):
    X.germToFunctionField W
      ((OpenLineFrameCoordinates318.frame M (U i) (frames i) W hi).symm
        (M.presheaf.map (homOfLE hV).op s))=
      ActualLineRationalEquations318.equation M U frames reference f₀ i:=by
  let T:X.Opens:=W⊓U reference
  letI:Nonempty T:=FunctionFieldGluing318.intersection_nonempty X W (U reference)
  have hTi:T≤U i:=inf_le_left.trans hi
  have hTr:T≤U reference:=inf_le_right
  have hTW:T≤W:=inf_le_left
  have hTV:T≤V:=hTW.trans hV
  have hanchorT:X.germToFunctionField T
      ((OpenLineFrameCoordinates318.frame M (U reference) (frames reference) T hTr).symm
        (M.presheaf.map (homOfLE hTV).op s))=f₀:=by
    rw [←restrict_chain M hTr href s,
      ←OpenLineFrameCoordinates318.inverse_natural M (U reference) (frames reference) le_rfl hTr,
      AffineDominantNormRestriction318.germ_restrict]
    exact hanchor
  have he:=ActualLineRationalEquations318.section_coefficient M U frames reference f₀
    i T hTi hTr (M.presheaf.map (homOfLE hTV).op s) hanchorT
  rw [←restrict_chain M hTW hV s,
    ←OpenLineFrameCoordinates318.inverse_natural M (U i) (frames i) hi hTW,
    AffineDominantNormRestriction318.germ_restrict] at he
  exact he
end ActualRationalSectionPropagation318
