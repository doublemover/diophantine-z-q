module
public import LineFrameReconstructionIso318
public import FunctionFieldGluing318
public section
noncomputable section
namespace ActualLineRationalEquations318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {X:Scheme.{u}} [IsIntegral X] (M:X.Modules) {ι:Type u}
    (U:ι→X.Opens) [∀i,Nonempty (U i)]
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
local instance overlapNonempty(i j:ι):Nonempty (U i⊓U j:X.Opens):=
  FunctionFieldGluing318.intersection_nonempty X (U i) (U j)
/-- The actual full-overlap transition, embedded into the SAME original
scheme function field through the genuine generic germ. -/
@[expose] def transitionGerm(i j:ι):X.functionField:=
  X.germToFunctionField (U i⊓U j)
    (LineFrameTransitions318.scalar M U frames i j (U i⊓U j) inf_le_left inf_le_right).val
lemma germ_on_subopen(i j:ι)(W:X.Opens)[Nonempty W](hi:W≤U i)(hj:W≤U j):
    X.germToFunctionField W (LineFrameTransitions318.scalar M U frames i j W hi hj).val=
      transitionGerm M U frames i j:=by
  have h:=congrArg Units.val
    (LineFrameTransitions318.restrict M U frames i j inf_le_left inf_le_right (le_inf hi hj))
  change X.presheaf.map (homOfLE (le_inf hi hj)).op
    (LineFrameTransitions318.scalar M U frames i j (U i⊓U j) inf_le_left inf_le_right).val=
      (LineFrameTransitions318.scalar M U frames i j W hi hj).val at h
  rw [←h,AffineDominantNormRestriction318.germ_restrict]
  rfl
lemma transition_ne(i j:ι):transitionGerm M U frames i j≠0:=by
  let e:=LineFrameTransitions318.scalar M U frames i j (U i⊓U j) inf_le_left inf_le_right
  have h:IsUnit (X.germToFunctionField (U i⊓U j) e.val):=
    e.isUnit.map (X.germToFunctionField (U i⊓U j)).hom
  exact h.ne_zero
lemma transition_comp(i j k:ι):
    transitionGerm M U frames i j*transitionGerm M U frames j k=
      transitionGerm M U frames i k:=by
  let W:X.Opens:=(U i⊓U j)⊓U k
  letI:Nonempty W:=FunctionFieldGluing318.intersection_nonempty X (U i⊓U j) (U k)
  have hi:W≤U i:=inf_le_left.trans inf_le_left
  have hj:W≤U j:=inf_le_left.trans inf_le_right
  have hk:W≤U k:=inf_le_right
  rw [←germ_on_subopen M U frames i j W hi hj,
    ←germ_on_subopen M U frames j k W hj hk,
    ←germ_on_subopen M U frames i k W hi hk,←map_mul]
  exact congrArg (X.germToFunctionField W)
    (congrArg Units.val (LineFrameTransitions318.comp M U frames i j k W hi hj hk))
lemma transition_self(i:ι):transitionGerm M U frames i i=1:=by
  unfold transitionGerm
  rw [LineFrameTransitions318.self]
  exact map_one _

variable (reference:ι)(f₀:X.functionField)(hf₀:f₀≠0)
/-- Local rational equations of the same rational line section, anchored
by an actual nonzero coefficient in one original frame. -/
@[expose] def equation(i:ι):X.functionField:=transitionGerm M U frames i reference*f₀
lemma equation_ne(i:ι):equation M U frames reference f₀ i≠0:=
  mul_ne_zero (transition_ne M U frames i reference) hf₀
lemma equation_reference:equation M U frames reference f₀ reference=f₀:=by
  rw [equation,transition_self,one_mul]
/-- Genuine Cartier-style local equation compatibility: the ratio is
an ACTUAL REGULAR UNIT on the complete overlap, not only a rational unit
or a pointwise equality of valuations. -/
theorem equation_ratio(i j:ι):
    equation M U frames reference f₀ i/equation M U frames reference f₀ j=
      X.germToFunctionField (U i⊓U j)
        (LineFrameTransitions318.scalar M U frames i j (U i⊓U j) inf_le_left inf_le_right).val:=by
  apply (div_eq_iff (equation_ne M U frames reference f₀ hf₀ j)).mpr
  change transitionGerm M U frames i reference*f₀=
    transitionGerm M U frames i j*(transitionGerm M U frames j reference*f₀)
  rw [←mul_assoc,transition_comp]
/-- Any genuine original section with the reference generic coefficient
has exactly the constructed rational equation as its coefficient in
every other original frame. This is an actual section comparison, not a
pointwise valuation assumption. -/
theorem section_coefficient(i:ι)(W:X.Opens)[Nonempty W]
    (hi:W≤U i)(hreference:W≤U reference)(s:Γ(M,W))
    (hanchor:X.germToFunctionField W
      ((OpenLineFrameCoordinates318.frame M (U reference) (frames reference) W hreference).symm s)=f₀):
    X.germToFunctionField W
      ((OpenLineFrameCoordinates318.frame M (U i) (frames i) W hi).symm s)=
        equation M U frames reference f₀ i:=by
  have hc:(OpenLineFrameCoordinates318.frame M (U i) (frames i) W hi).symm s=
      (LineFrameTransitions318.scalar M U frames i reference W hi hreference).val*
        (OpenLineFrameCoordinates318.frame M (U reference) (frames reference) W hreference).symm s:=by
    apply (OpenLineFrameCoordinates318.frame M (U i) (frames i) W hi).injective
    rw [LinearEquiv.apply_symm_apply,LineFrameTransitions318.relation,
      LinearEquiv.apply_symm_apply]
  rw [hc,map_mul,germ_on_subopen,hanchor]
  rfl
/-- The line of these actual transition units is the unchanged original
line sheaf. This constructs the local-equation presentation; it does not
identify an unrelated coefficient Finsupp with a Cartier-divisor class. -/
@[expose] def associatedLineIso(hcover:(⊤:X.Opens)≤⨆i,U i):
    M≅CocycleModule318.object U (LineFrameCocycle318.cocycle M U frames):=
  LineFrameReconstructionIso318.iso M U frames hcover
end ActualLineRationalEquations318
