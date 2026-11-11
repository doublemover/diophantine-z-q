module
public import InverseLineSectionContraction318
public section
noncomputable section
namespace LineArrowInverseLocal318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace LineSheafClass318
open ModuleLocalGluing318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : Line X) (f : L.object ⟶ SheafOfModules.unit X.ringCatSheaf)
local notation "I" => FramedLineInverse318.inverse L
abbrev frame (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :=
  OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) V h
abbrev inverseFrame (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :=
  OpenLineFrameCoordinates318.frame I.object (L.opens i) (I.frame i) V h

/-- The actual value of the original ideal inclusion on its frame generator. -/
@[expose] def coefficient (i : L.Index) (V : X.Opens) (h : V≤L.opens i) : Γ(X,V) :=
  f.app V (frame L i V h 1)

lemma coefficient_natural (i : L.Index) (V W : X.Opens)
    (hV : V≤L.opens i) (hW : W≤V) :
    X.presheaf.map (homOfLE hW).op (coefficient L f i V hV)=
      coefficient L f i W (hW.trans hV) := by
  have hn := congrArg (fun k => k (frame L i V hV 1)) (f.val.naturality (homOfLE hW).op)
  change X.presheaf.map (homOfLE hW).op (f.app V (frame L i V hV 1))=_
  rw [← hn,OpenLineFrameCoordinates318.natural,map_one]
  rfl

lemma coefficient_transition (i j : L.Index) (V : X.Opens)
    (hi : V≤L.opens i) (hj : V≤L.opens j) :
    coefficient L f j V hj =
      X.presheaf.map (homOfLE (le_inf hi hj)).op
        ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j).val *
          coefficient L f i V hi := by
  have he := LineFrameCocycle318.relation L.object L.opens L.frame i j V
    (le_inf hi hj) (1 : Γ(X,V))
  simp only [mul_one] at he
  have hh := congrArg (fun s => f.app V s) he
  let u := X.presheaf.map (homOfLE (le_inf hi hj)).op
    ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j).val
  change f.app V (frame L j V hj 1)=u*f.app V (frame L i V hi 1)
  calc
    _ = f.app V (frame L i V hi u) := hh.symm
    _ = f.app V (u • frame L i V hi 1) := by
      congr 1
      rw [← (frame L i V hi).map_smul,smul_eq_mul,mul_one]
    _ = _ := (f.val.app (op V)).hom.map_smul u _

/-- The inclusion coefficients in the genuine inverse frames, on every
original subopen. The inverse transition compensates the frame change. -/
@[expose] def localMap (i : L.Index) (V : X.Opens) (h : V≤L.opens i) :
    Γ(X,V) →ₗ[Γ(X,V)] Γ(I.object,V) :=
  (inverseFrame L i V h).toLinearMap.comp
    { toFun := fun a => a*coefficient L f i V h
      map_add' := fun a b => add_mul a b _
      map_smul' := fun a b => mul_assoc a b _ }

lemma natural (i : L.Index) (V W : X.Opens) (hV : V≤L.opens i) (hW : W≤V)
    (a : Γ(X,V)) :
    res I.object hW (localMap L f i V hV a)=
      localMap L f i W (hW.trans hV) (X.presheaf.map (homOfLE hW).op a) := by
  change res I.object hW (inverseFrame L i V hV (a*coefficient L f i V hV))=_
  rw [OpenLineFrameCoordinates318.natural,map_mul,coefficient_natural]
  rfl

lemma compatible (i j : L.Index) (V : X.Opens) (hi : V≤L.opens i) (hj : V≤L.opens j)
    (a : Γ(X,V)) : localMap L f i V hi a=localMap L f j V hj a := by
  have he := LineFrameCocycle318.relation I.object L.opens I.frame i j V
    (le_inf hi hj) (a*coefficient L f j V hj)
  have hu : (LineFrameCocycle318.cocycle I.object L.opens I.frame).transition i j =
      ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j)⁻¹ :=
    congrArg (fun q => q.transition i j)
      (LineSheafInverse318.original_inverse_transitions L.object L.opens L.frame)
  rw [hu,coefficient_transition L f i j V hi hj] at he
  let u := (LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j
  let r := X.presheaf.map (homOfLE (le_inf hi hj)).op
  have hh : r (u⁻¹).val * (a*(r u.val*coefficient L f i V hi)) =
      a*coefficient L f i V hi := by
    calc
      _ = (r (u⁻¹).val*r u.val)*(a*coefficient L f i V hi) := by ring
      _ = _ := by rw [← map_mul,Units.inv_mul,map_one,one_mul]
  change inverseFrame L i V hi (a*coefficient L f i V hi)=_
  rw [hh] at he
  exact he
end LineArrowInverseLocal318
