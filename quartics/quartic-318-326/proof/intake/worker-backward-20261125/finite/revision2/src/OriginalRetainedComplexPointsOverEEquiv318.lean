module
public import OriginalRetainedComplexPointFromE318

@[expose] public section
noncomputable section

namespace OriginalRetainedComplexPointsOverEEquiv318
open AlgebraicGeometry CategoryTheory Limits
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedComplexPointFromE318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
universe u

variable {A Y E T:Scheme.{u}} (a:A⟶Y) (P:E⟶Y) (σ:T⟶E)
local notation "G" => fiber a P
local notation "H" => fiber a (σ≫P)
local notation "I" => iter a P σ
local notation "PtC" => Over.mk (𝟙 T)⟶H
local notation "PtE" => Over.mk σ⟶G

theorem iter_cancel_right :
    (I).hom.left≫(I).inv.left=𝟙 (pullback (G).hom σ) := by
  exact congrArg (fun v:(fiber (G).hom σ)⟶(fiber (G).hom σ)=>v.left) (I).hom_inv_id

theorem iter_cancel_left :
    (I).inv.left≫(I).hom.left=𝟙 (H).left := by
  exact congrArg (fun v:H⟶H=>v.left) (I).inv_hom_id

def toIterated (p:PtC) : T⟶pullback (G).hom σ :=
  p.left≫(I).inv.left

theorem toIterated_base (p:PtC) :
    toIterated a P σ p≫pullback.snd (G).hom σ=𝟙 T :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k=>p.left≫k) (Over.w (I).inv)).trans p.w)

/-- Take the one already constructed original complex point and read it
as a point with the selected E-coefficient morphism. Not a new complex
point or an analytic comparison. The map to Spec E is literally σ. -/
def readOverE (p:PtC) : PtE :=
  let q := toIterated a P σ p
  Over.homMk (q≫pullback.fst (G).hom σ)
    (calc
      _ = q≫(pullback.fst (G).hom σ≫(G).hom) := Category.assoc _ _ _
      _ = q≫(pullback.snd (G).hom σ≫σ) :=
        congrArg (fun k=>q≫k) pullback.condition
      _ = (q≫pullback.snd (G).hom σ)≫σ := (Category.assoc _ _ _).symm
      _ = (𝟙 T)≫σ := congrArg (fun k=>k≫σ) (toIterated_base a P σ p)
      _ = σ := Category.id_comp _)

theorem readOverE_of_lift (p:PtE) :
    readOverE a P σ (complexPoint a P σ p)=p := by
  apply Over.OverMorphism.ext
  let h : p.left≫(G).hom=(𝟙 T)≫σ := p.w.trans (Category.id_comp σ).symm
  let r := pullback.lift p.left (𝟙 T) h
  have cancel : toIterated a P σ (complexPoint a P σ p)=r := by
    change (r≫(I).hom.left)≫(I).inv.left=_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k=>r≫k) (iter_cancel_right a P σ)).trans (Category.comp_id _))
  change toIterated a P σ (complexPoint a P σ p)≫pullback.fst (G).hom σ=p.left
  exact (congrArg (fun k=>k≫pullback.fst (G).hom σ) cancel).trans
    (pullback.lift_fst p.left (𝟙 T) h)

theorem lift_of_readOverE (p:PtC) :
    complexPoint a P σ (readOverE a P σ p)=p := by
  apply Over.OverMorphism.ext
  let q := readOverE a P σ p
  let h : q.left≫(G).hom=(𝟙 T)≫σ := q.w.trans (Category.id_comp σ).symm
  let r := pullback.lift q.left (𝟙 T) h
  have reads : r=toIterated a P σ p := by
    apply pullback.hom_ext
    · exact pullback.lift_fst q.left (𝟙 T) h
    · exact (pullback.lift_snd q.left (𝟙 T) h).trans (toIterated_base a P σ p).symm
  change r≫(I).hom.left=p.left
  exact (congrArg (fun k=>k≫(I).hom.left) reads).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k=>p.left≫k) (iter_cancel_left a P σ)).trans (Category.comp_id _)))

def exactPoints : PtE≃PtC where
  toFun := complexPoint a P σ
  invFun := readOverE a P σ
  left_inv := readOverE_of_lift a P σ
  right_inv := lift_of_readOverE a P σ

/-- An original selected analytic point can be supplied once on the
actual complex 33-fibre. Its E-relative read is forced; any already
recorded relative read is equal if it has that whole complex lift. -/
theorem readOverE_unique (p:PtC) (e:PtE) (h:complexPoint a P σ e=p) :
    readOverE a P σ p=e :=
  (congrArg (readOverE a P σ) h.symm).trans (readOverE_of_lift a P σ e)

theorem readOverE_mul [MonObj (Over.mk a)] (p q:PtC):
    readOverE a P σ (p*q)=readOverE a P σ p*readOverE a P σ q := by
  apply (exactPoints a P σ).injective
  exact
    (lift_of_readOverE a P σ (p*q)).trans
      ((complexPoint_mul a P σ (readOverE a P σ p) (readOverE a P σ q)).trans
        (congrArg₂ (·*·) (lift_of_readOverE a P σ p) (lift_of_readOverE a P σ q))).symm

end OriginalRetainedComplexPointsOverEEquiv318
