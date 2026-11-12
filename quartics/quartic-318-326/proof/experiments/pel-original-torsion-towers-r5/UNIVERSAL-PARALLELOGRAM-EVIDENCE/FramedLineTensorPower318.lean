module
public import TensorLineCocycle318
public import StructureLineFrames318
public import UnitCocyclePower318
public import LineFrameReconstructionIso318
public import CocycleEqualityTransport318
public section
noncomputable section
namespace FramedLineTensorPower318
open AlgebraicGeometry CategoryTheory IntrinsicTensorSheaf318
set_option maxHeartbeats 350000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}}
/-- Genuine iterated tensor sheaves: zero is O and successor tensors the
previous actual sheaf with the unchanged original module. -/
@[expose] def object (M:X.Modules):ℕ→X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n+1 => tensor (object M n) M
lemma object_zero (M:X.Modules):object M 0=SheafOfModules.unit X.ringCatSheaf:=rfl
lemma object_succ (M:X.Modules) (n:ℕ):object M (n+1)=tensor (object M n) M:=rfl
variable (M:X.Modules) {ι:Type u} (U:ι→X.Opens)
    (em:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
/-- Genuine unit frames on the same unchanged original cover at every power. -/
@[expose] def frames (n:ℕ):∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅(object M n).restrict (U i).ι:=
  Nat.rec (motive:=fun k=>∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅(object M k).restrict (U i).ι)
    (fun i=>StructureLineFrames318.frame X (U i))
    (fun k ih i=>TensorLineLocalFrame318.frame (object M k) M (U i) (ih i) (em i)) n
lemma cocycle_eq (n:ℕ):
    LineFrameCocycle318.cocycle (object M n) U (frames M U em n)=
      UnitCocyclePower318.power (LineFrameCocycle318.cocycle M U em) n:=by
  induction n with
  | zero =>
    apply UnitTransitionCocycle318.Cocycle.ext
    intro i j
    change (LineFrameCocycle318.cocycle (SheafOfModules.unit X.ringCatSheaf) U
      (fun k=>StructureLineFrames318.frame X (U k))).transition i j=_^0
    rw [pow_zero]
    exact StructureLineFrames318.transition_one X U i j
  | succ n ih =>
    change LineFrameCocycle318.cocycle (tensor (object M n) M) U
      (TensorLineCocycle318.frames (object M n) M U (frames M U em n) em)=_
    exact (TensorLineCocycle318.cocycle_eq (object M n) M U (frames M U em n) em).trans
      ((congrArg (fun c=>UnitCocycleProduct318.product c (LineFrameCocycle318.cocycle M U em)) ih).trans
        (UnitCocyclePower318.succ _ n).symm)
lemma transition (n:ℕ) (i j:ι):
    (LineFrameCocycle318.cocycle (object M n) U (frames M U em n)).transition i j=
      (LineFrameCocycle318.cocycle M U em).transition i j^n:=
  congrArg (fun c=>c.transition i j) (cocycle_eq M U em n)
variable (hc:(⊤:X.Opens)≤⨆i,U i)
/-- The original iterated tensor sheaf is reconstructed as the actual
coefficient module of the proved nth powers of its original transition units. -/
@[expose] def iso (n:ℕ):object M n≅CocycleModule318.object U
    (UnitCocyclePower318.power (LineFrameCocycle318.cocycle M U em) n):=
  CocycleEqualityTransport318.changeTarget U
    (LineFrameReconstructionIso318.iso (object M n) U (frames M U em n) hc) (cocycle_eq M U em n)
lemma hom_inv (n:ℕ):(iso M U em hc n).hom≫(iso M U em hc n).inv=𝟙 _:=
  (iso M U em hc n).hom_inv_id
lemma inv_hom (n:ℕ):(iso M U em hc n).inv≫(iso M U em hc n).hom=𝟙 _:=
  (iso M U em hc n).inv_hom_id
lemma coefficient (n:ℕ) (i:ι):
    (iso M U em hc n).hom≫CocycleModule318.coefficient U
      (UnitCocyclePower318.power (LineFrameCocycle318.cocycle M U em) n) i=
    LineFrameAdjunction318.coordinate (object M n) (U i) (frames M U em n i):=
  (CocycleEqualityTransport318.changeTarget_coefficient U
    (LineFrameReconstructionIso318.iso (object M n) U (frames M U em n) hc) (cocycle_eq M U em n) i).trans
      (LineFrameReconstructionIso318.hom_coefficient (object M n) U (frames M U em n) hc i)
@[expose] def eighthIso:object M 8≅CocycleModule318.object U
    (UnitCocyclePower318.power (LineFrameCocycle318.cocycle M U em) 8):=iso M U em hc 8
end FramedLineTensorPower318
