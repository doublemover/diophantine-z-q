module

public import SelectedSameAActualNilpotentLineGluing318
public import ModuleGlobalSections318
public import Mathlib.Tactic.Ring

/-!
Actual frame sections of the same principal-unit line. Their
epsilon multiples glue globally; the unmultiplied generators
have the exact signed difference on the whole overlap.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitMarkedFrame318
open SelectedSameAActualNilpotentLineGluing318 OpenLineFrameCoordinates318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {I : Type u} (V : I → X.Opens) (M : X.Modules)
variable (f : ∀ i, SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ M.restrict (V i).ι)
variable (e : Γ(X,⊤)) (he : e * e = 0) (c : AdditiveCocycle V)
variable (hframe : LineFrameCocycle318.cocycle M V f = unitCocycle V e he c)

@[expose] def gen (i : I) : Γ(M,V i) :=
  frame M (V i) (f i) (V i) le_rfl (1 : Γ(X,V i))

@[expose] def epsGen (i : I) : Γ(M,V i) :=
  frame M (V i) (f i) (V i) le_rfl (epsilonOn e (V i))

include hframe in
/-- Re-expression from the right actual frame into the left actual
frame, on the whole original overlap. -/
theorem frame_on_overlap (i j : I) (b : Γ(X,V i ⊓ V j)) :
    frame M (V i) (f i) (V i ⊓ V j) inf_le_left
      ((1 + epsilonOn e (V i ⊓ V j) * c.coeff i j) * b) =
    frame M (V j) (f j) (V i ⊓ V j) inf_le_right b := by
  have h := LineFrameTransitions318.relation M V f i j
    (V i ⊓ V j) inf_le_left inf_le_right b
  change frame M (V i) (f i) (V i ⊓ V j) inf_le_left
      (((LineFrameCocycle318.cocycle M V f).transition i j).val * b) =
    frame M (V j) (f j) (V i ⊓ V j) inf_le_right b at h
  rw [hframe] at h
  change frame M (V i) (f i) (V i ⊓ V j) inf_le_left
    ((nilUnit (epsilonOn e (V i ⊓ V j)) (epsilonOn_sq e he (V i ⊓ V j))
      (c.coeff i j)).val * b) = _ at h
  rw [nilUnit_val] at h
  exact h

include hframe in
/-- The original chosen generators have the actual right-minus-left
sign. The output lives in the same evaluated line, not in the old KS
extension or a newly chosen module. -/
theorem signed_difference (i j : I) :
    M.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (gen V M f j) -
    M.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (gen V M f i) =
      frame M (V i) (f i) (V i ⊓ V j) inf_le_left
        (epsilonOn e (V i ⊓ V j) * c.coeff i j) := by
  let rj := homOfLE (inf_le_right : V i ⊓ V j ≤ V j)
  let ri := homOfLE (inf_le_left : V i ⊓ V j ≤ V i)
  have hj₀ : X.presheaf.map rj.op (1 : Γ(X,V j)) = (1 : Γ(X,V i ⊓ V j)) :=
    map_one (X.presheaf.map rj.op).hom
  have hi₀ : X.presheaf.map ri.op (1 : Γ(X,V i)) = (1 : Γ(X,V i ⊓ V j)) :=
    map_one (X.presheaf.map ri.op).hom
  have hj : M.presheaf.map rj.op (gen V M f j) =
      frame M (V j) (f j) (V i ⊓ V j) inf_le_right (1 : Γ(X,V i ⊓ V j)) :=
    (OpenLineFrameCoordinates318.natural M (V j) (f j) le_rfl inf_le_right
      (1 : Γ(X,V j))).trans
      (congrArg (fun b : Γ(X,V i ⊓ V j) => frame M (V j) (f j) _ inf_le_right b) hj₀)
  have hi : M.presheaf.map ri.op (gen V M f i) =
      frame M (V i) (f i) (V i ⊓ V j) inf_le_left (1 : Γ(X,V i ⊓ V j)) :=
    (OpenLineFrameCoordinates318.natural M (V i) (f i) le_rfl inf_le_left
      (1 : Γ(X,V i))).trans
      (congrArg (fun b : Γ(X,V i ⊓ V j) => frame M (V i) (f i) _ inf_le_left b) hi₀)
  have h := frame_on_overlap V M f e he c hframe i j 1
  rw [mul_one] at h
  change M.presheaf.map rj.op (gen V M f j) - M.presheaf.map ri.op (gen V M f i) = _
  rw [hj, hi, ← h, ← map_sub]
  congr 1
  ring

include hframe in
theorem eps_compatible : TopCat.Presheaf.IsCompatible M.presheaf V (epsGen V M f e) := by
  intro i j
  change M.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
      (epsGen V M f e i) =
    M.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
      (epsGen V M f e j)
  unfold epsGen
  rw [OpenLineFrameCoordinates318.natural M (V i) (f i) le_rfl inf_le_left,
    OpenLineFrameCoordinates318.natural M (V j) (f j) le_rfl inf_le_right]
  have hi := epsilonOn_restrict e (inf_le_left : V i ⊓ V j ≤ V i)
  have hj := epsilonOn_restrict e (inf_le_right : V i ⊓ V j ≤ V j)
  change X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
      (epsilonOn e (V i)) = epsilonOn e (V i ⊓ V j) at hi
  change X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
      (epsilonOn e (V j)) = epsilonOn e (V i ⊓ V j) at hj
  rw [hi, hj]
  have h := frame_on_overlap V M f e he c hframe i j (epsilonOn e (V i ⊓ V j))
  have heps := epsilonOn_sq e he (V i ⊓ V j)
  have hm : (1 + epsilonOn e (V i ⊓ V j) * c.coeff i j) * epsilonOn e (V i ⊓ V j) =
      epsilonOn e (V i ⊓ V j) := by
    calc
      _ = epsilonOn e (V i ⊓ V j) +
          (epsilonOn e (V i ⊓ V j) * epsilonOn e (V i ⊓ V j)) * c.coeff i j := by ring
      _ = _ := by rw [heps, zero_mul, add_zero]
  rw [hm] at h
  exact h

/-- This is a real global epsilon-lift section of the original line;
there is not in general a global lift of the reduced frame itself. -/
@[expose] def epsilonLiftSection (hc : (⊤ : X.Opens) ≤ ⨆ i, V i) : Γ(M,⊤) :=
  ModuleGlobalSections318.gluedTop M V hc (epsGen V M f e)
    (eps_compatible V M f e he c hframe)

include hframe in
theorem epsilonLift_on_chart (hc : (⊤ : X.Opens) ≤ ⨆ i, V i) (i : I) :
    M.presheaf.map (homOfLE (show V i ≤ ⊤ from le_top)).op
      (epsilonLiftSection V M f e he c hframe hc) = epsGen V M f e i :=
  ModuleGlobalSections318.gluedTop_restrict M V hc (epsGen V M f e)
    (eps_compatible V M f e he c hframe) i

end SelectedSameAPrincipalUnitMarkedFrame318
