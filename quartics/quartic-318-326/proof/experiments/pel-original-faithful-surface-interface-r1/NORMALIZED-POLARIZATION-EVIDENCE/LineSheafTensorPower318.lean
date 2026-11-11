module
public import FramedLineTensorPower318
public import LineSheafClassGroup318
public section
noncomputable section
namespace LineSheafTensorPower318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}}
/-- An actual iterated tensor line on the original unchanged covering family. -/
@[expose] def line (L:Line X) (n:ℕ):Line X where
  object:=FramedLineTensorPower318.object L.object n
  Index:=L.Index
  opens:=L.opens
  cover:=L.cover
  frame:=FramedLineTensorPower318.frames L.object L.opens L.frame n
/-- Only the actual underlying objects are compared; the source and unit
cover records are not identified. -/
@[expose] def zeroIso (L:Line X):(line L 0).object≅(LineSheafUnit318.line X).object:=Iso.refl _
/-- The same-cover power and the pairwise-cover tensor product have the same
actual tensor sheaf, without asserting equality of presentation records. -/
@[expose] def succIso (L:Line X) (n:ℕ):
    (line L (n+1)).object≅(LineSheafTensor318.line (line L n) L).object:=Iso.refl _
lemma classOf_power (L:Line X) (n:ℕ):classOf (line L n)=(classOf L)^n:=by
  induction n with
  | zero =>
    exact (classOf_eq (zeroIso L)).trans LineSheafClassGroup318.classOf_structure
  | succ n ih =>
    calc
      classOf (line L (n+1))=classOf (LineSheafTensor318.line (line L n) L):=
        classOf_eq (succIso L n)
      _=classOf (line L n)*classOf L:=LineSheafClassGroup318.classOf_tensor _ _
      _=(classOf L)^(n+1):=by rw [ih,pow_succ]
/-- Exact object-level comparison with nth powers of the original transition
units on the unchanged original cover. -/
@[expose] def iso (L:Line X) (n:ℕ):(line L n).object≅
    CocycleModule318.object L.opens
      (UnitCocyclePower318.power (LineFrameCocycle318.cocycle L.object L.opens L.frame) n):=
  FramedLineTensorPower318.iso L.object L.opens L.frame L.cover n
lemma hom_inv (L:Line X) (n:ℕ):(iso L n).hom≫(iso L n).inv=𝟙 _ :=(iso L n).hom_inv_id
lemma inv_hom (L:Line X) (n:ℕ):(iso L n).inv≫(iso L n).hom=𝟙 _ :=(iso L n).inv_hom_id
lemma classOf_eighth (L:Line X):classOf (line L 8)=(classOf L)^8:=classOf_power L 8
@[expose] def eighthIso (L:Line X):(line L 8).object≅
    CocycleModule318.object L.opens
      (UnitCocyclePower318.power (LineFrameCocycle318.cocycle L.object L.opens L.frame) 8):=iso L 8
end LineSheafTensorPower318
