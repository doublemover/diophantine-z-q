module
public import OriginalRetainedComplexZeroByPasting318
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

@[expose] public section
noncomputable section
set_option maxRecDepth 5500
namespace OriginalRetainedComplexPointProducts318
open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory
open OriginalRetainedComplexZeroByPasting318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
universe u

/-- The group law of a marked family evaluated on two points of one
literal common base. The explicit pullback pair records that base. -/
def productOn {Y W:Scheme.{u}} (A:Over Y) [MonObj A] (w:W⟶Y)
    (p q:Over.mk w⟶A):W⟶A.left :=
  (p*q).left

theorem productOn_push {Y W:Scheme.{u}} (A:Over Y) [MonObj A] (w:W⟶Y)
    (p q:Over.mk w⟶A):
    productOn A w p q=(lift p q).left≫(μ[A]).left := rfl

def projectPoint {Y S W:Scheme.{u}} (A:Over Y) (f:S⟶Y) (w:W⟶S)
    (p:Over.mk w⟶(Over.pullback f).obj A):Over.mk (w≫f)⟶A :=
  Over.homMk (p.left≫pullback.fst A.hom f)
    (by rw [Category.assoc,pullback.condition,←Category.assoc]; exact congrArg (·≫f) p.w)

@[reassoc] theorem projected_mul {Y S W:Scheme.{u}} (A:Over Y) [MonObj A]
    (f:S⟶Y) (w:W⟶S) (p q:Over.mk w⟶(Over.pullback f).obj A):
    (p*q).left≫pullback.fst A.hom f =
      (projectPoint A f w p * projectPoint A f w q).left := by
  let F:=Over.pullback f
  let c:=(Functor.LaxMonoidal.μ F A A).left
  have identify :
      (lift p q).left≫c≫pullback.fst (A⊗A).hom f =
        (lift (projectPoint A f w p) (projectPoint A f w q)).left := by
    apply Over.tensorObj_ext
    · have m : c≫pullback.fst (A⊗A).hom f≫pullback.fst A.hom A.hom =
          pullback.fst (F.obj A).hom (F.obj A).hom≫pullback.fst A.hom f :=
        Over.μ_pullback_left_fst_fst (f:=f) A A
      have first : (lift p q).left≫pullback.fst (F.obj A).hom (F.obj A).hom=p.left := by
        simpa only [Over.lift_left] using pullback.lift_fst p.left q.left (p.w.trans q.w.symm)
      calc
        _ = (lift p q).left≫(c≫pullback.fst (A⊗A).hom f≫pullback.fst A.hom A.hom) := by
          simp only [Category.assoc]
        _ = (lift p q).left≫(pullback.fst (F.obj A).hom (F.obj A).hom≫pullback.fst A.hom f) :=
          congrArg (fun a=>(lift p q).left≫a) m
        _ = p.left≫pullback.fst A.hom f :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun a=>a≫pullback.fst A.hom f) first)
        _ = _ := by
          let p' := projectPoint A f w p
          let q' := projectPoint A f w q
          change p'.left=(lift p' q').left≫pullback.fst A.hom A.hom
          simpa only [Over.lift_left] using
            (pullback.lift_fst p'.left q'.left (p'.w.trans q'.w.symm)).symm
    · have m : c≫pullback.fst (A⊗A).hom f≫pullback.snd A.hom A.hom =
          pullback.snd (F.obj A).hom (F.obj A).hom≫pullback.fst A.hom f :=
        Over.μ_pullback_left_fst_snd (f:=f) A A
      have second : (lift p q).left≫pullback.snd (F.obj A).hom (F.obj A).hom=q.left := by
        simpa only [Over.lift_left] using pullback.lift_snd p.left q.left (p.w.trans q.w.symm)
      calc
        _ = (lift p q).left≫(c≫pullback.fst (A⊗A).hom f≫pullback.snd A.hom A.hom) := by
          simp only [Category.assoc]
        _ = (lift p q).left≫(pullback.snd (F.obj A).hom (F.obj A).hom≫pullback.fst A.hom f) :=
          congrArg (fun a=>(lift p q).left≫a) m
        _ = q.left≫pullback.fst A.hom f :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun a=>a≫pullback.fst A.hom f) second)
        _ = _ := by
          let p' := projectPoint A f w p
          let q' := projectPoint A f w q
          change q'.left=(lift p' q').left≫pullback.snd A.hom A.hom
          simpa only [Over.lift_left] using
            (pullback.lift_snd p'.left q'.left (p'.w.trans q'.w.symm)).symm
  have projection : (F.map (μ[A])).left≫pullback.fst A.hom f =
      pullback.fst (A⊗A).hom f≫(μ[A]).left := by
    simp only [F,Over.pullback_map_left,pullback.lift_fst]
  change ((lift p q).left≫(c≫(F.map (μ[A])).left))≫pullback.fst A.hom f = _
  calc
    _ = (lift p q).left≫c≫(F.map (μ[A])).left≫pullback.fst A.hom f := by
      simp only [Category.assoc]
    _ = (lift p q).left≫c≫pullback.fst (A⊗A).hom f≫(μ[A]).left := by
      rw [projection]
    _ = ((lift p q).left≫c≫pullback.fst (A⊗A).hom f)≫(μ[A]).left := by
      simp only [Category.assoc]
    _ = _ := by
      rw [identify]
      rfl

variable {A₃₃ A₃ Y₃₃ Y₃:Scheme.{u}} (a₃₃:A₃₃⟶Y₃₃) (a₃:A₃⟶Y₃)
  (forget:Y₃₃⟶Y₃) (u₀:A₃₃⟶A₃) (cart:IsPullback u₀ a₃₃ a₃ forget)
local notation "A" => Over.mk a₃₃
local notation "B" => Over.mk a₃
local notation "U" => Iso.hom (universal a₃₃ a₃ forget u₀ cart)

include cart in
theorem product_universal_projection [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom]
    {W:Scheme.{u}} (w:W⟶Y₃₃) (p q:Over.mk w⟶A) :
    (p*q).left≫u₀ =
      (projectPoint B forget w (p≫U)*projectPoint B forget w (q≫U)).left := by
  have how : (U).left≫pullback.fst a₃ forget=u₀ := cart.isoPullback_hom_fst
  have h := congrArg (fun r=>(r:Over.mk w⟶fiber a₃ forget).left≫pullback.fst a₃ forget)
    (MonObj.mul_comp p q U)
  change ((p*q).left≫(U).left)≫pullback.fst a₃ forget =
    ((p≫U)*(q≫U)).left≫pullback.fst a₃ forget at h
  rw [Category.assoc,how] at h
  exact h.trans (projected_mul B forget w (p≫U) (q≫U))

variable {L E C:Type u} [Field L] [Field E] [Field C] (i:L→+*E) (σ:E→+*C)
  (x:Spec (.of E)⟶Y₃₃) (xL:Spec (.of L)⟶Y₃)
  (named:specOf i≫xL=x≫forget)
local notation "T" => Spec (CommRingCat.of C)
local notation "xC" => specOf σ≫x
local notation "yC" => specOf (σ.comp i)≫xL
local notation "A_C" => fiber a₃₃ xC
local notation "B_C" => fiber a₃ yC
local notation "Φ" => Iso.hom (complex a₃₃ a₃ forget u₀ cart i σ x xL named)
local notation "eT" => (𝟙 T)

include cart named in
theorem same_projection (p:Over.mk eT⟶A_C) :
    (projectPoint B yC eT (p≫Φ)).left =
      (projectPoint B forget (eT≫xC)
        ((projectPoint A xC eT p)≫U)).left := by
  change (p.left≫(Φ).left)≫pullback.fst a₃ yC =
    ((p.left≫pullback.fst a₃₃ xC)≫(U).left)≫pullback.fst a₃ forget
  have hu:(U).left≫pullback.fst a₃ forget=u₀ := cart.isoPullback_hom_fst
  simp only [Category.assoc,complex_projection,hu]

variable [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
  [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom]

include cart named in
/-- The strict selected complex forget arrow carries multiplication of
the actual scheme points. Both projections are used; no comparison on
coarse moduli points and no zero-only group inference occurs. -/
theorem complex_points_product (p q:Over.mk eT⟶A_C) :
    (p*q)≫Φ=(p≫Φ)*(q≫Φ) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · let p':=projectPoint A xC eT p
    let q':=projectPoint A xC eT q
    let pL:=projectPoint B forget (eT≫xC) (p'≫U)
    let qL:=projectPoint B forget (eT≫xC) (q'≫U)
    let p₁:=projectPoint B yC eT (p≫Φ)
    let q₁:=projectPoint B yC eT (q≫Φ)
    have hp:p₁.left=pL.left := same_projection a₃₃ a₃ forget u₀ cart i σ x xL named p
    have hq:q₁.left=qL.left := same_projection a₃₃ a₃ forget u₀ cart i σ x xL named q
    calc
      _ = ((p*q).left≫pullback.fst a₃₃ xC)≫u₀ :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun a=>(p*q).left≫a)
            (complex_projection a₃₃ a₃ forget u₀ cart i σ x xL named)).trans
            (Category.assoc _ _ _).symm)
      _ = (p'*q').left≫u₀ :=
        congrArg (fun a=>a≫u₀) (projected_mul A xC eT p q)
      _ = (pL*qL).left := product_universal_projection a₃₃ a₃ forget u₀ cart (eT≫xC) p' q'
      _ = (p₁*q₁).left := by
        simp only [Hom.mul_def,Over.comp_left,Over.lift_left]
        simp only [hp,hq]
      _ = _ := (projected_mul B yC eT (p≫Φ) (q≫Φ)).symm
  · exact (((p*q)≫Φ).w).trans (((p≫Φ)*(q≫Φ)).w).symm

include cart named in
/-- Consume the one analytic additive map at complex level 33; its
actual original x3 image is automatically additive. No extra analytic
map into x3 or independently asserted x3 group identity is needed. -/
theorem complex_add_from_original {Z:Type u} [Add Z]
    (Q:Z→(Over.mk eT⟶A_C)) (added:∀z w:Z,Q (z+w)=(Q z)*(Q w)) (z w:Z):
    (Q (z+w))≫Φ=((Q z)≫Φ)*((Q w)≫Φ) := by
  rw [added,complex_points_product]

end OriginalRetainedComplexPointProducts318
