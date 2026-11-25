module
public import OriginalRetainedComplexPointProducts318

@[expose] public section
noncomputable section
set_option maxRecDepth 4600

namespace OriginalRetainedComplexPointFromE318
open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory
open OriginalRetainedComplexZeroByPasting318 OriginalRetainedComplexPointProducts318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
universe u

section LiftOriginalE
variable {A Y E T:Scheme.{u}} (a:A⟶Y) (x:E⟶Y) (f:T⟶E)

local notation "F" => fiber a x
local notation "F_C" => fiber a (f≫x)
local notation "I" => Iso.hom (iter a x f)

/-- The literal pullback of the given E-point with complex coefficient
map f, followed by the strict pasted field square. -/
def complexPoint (p:Over.mk f⟶F):Over.mk (𝟙 T)⟶F_C := by
  let h : p.left≫(F).hom=(𝟙 T)≫f := p.w.trans (Category.id_comp f).symm
  let first : T⟶pullback (F).hom f := pullback.lift p.left (𝟙 T) h
  have base : (I).left≫(F_C).hom=pullback.snd (F).hom f := Over.w I
  exact Over.homMk (first≫(I).left) ((Category.assoc _ _ _).trans
    ((congrArg (fun b=>first≫b) base).trans (pullback.lift_snd p.left (𝟙 T) h)))

@[reassoc] theorem complexPoint_project (p:Over.mk f⟶F):
    (complexPoint a x f p).left≫pullback.fst a (f≫x) =
      p.left≫pullback.fst a x := by
  let h : p.left≫(F).hom=(𝟙 T)≫f := p.w.trans (Category.id_comp f).symm
  let first : T⟶pullback (F).hom f := pullback.lift p.left (𝟙 T) h
  change (first≫(I).left)≫pullback.fst a (f≫x) = _
  calc
    _ = first≫((I).left≫pullback.fst a (f≫x)) := Category.assoc _ _ _
    _ = first≫(pullback.fst (F).hom f≫pullback.fst a x) :=
      congrArg (fun b=>first≫b) (iter_read a x f)
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun b=>b≫pullback.fst a x) (pullback.lift_fst p.left (𝟙 T) h))

/-- Only underlying representatives matter for the actual product in the
same total group. In particular (1_T ≫ f) ≫ x versus f ≫ x does not create
a new choice of a point in the total space. -/
theorem product_congr_left {Y' W:Scheme.{u}} (D:Over Y') [MonObj D]
    {h h':W⟶Y'} {p q:Over.mk h⟶D} {p' q':Over.mk h'⟶D}
    (hp:p.left=p'.left) (hq:q.left=q'.left):
    (p*q).left=(p'*q').left := by
  simp only [Hom.mul_def,Over.comp_left,Over.lift_left,hp,hq]

/-- Base-change of the actual points of the one selected E-object
preserves addition. The first projection checks the original total
group and the second checks the literal complex field point. -/
theorem complexPoint_mul [MonObj (Over.mk a)] (p q:Over.mk f⟶F):
    complexPoint a x f (p*q)=complexPoint a x f p*complexPoint a x f q := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · let p₀ := projectPoint (Over.mk a) x f p
    let q₀ := projectPoint (Over.mk a) x f q
    let p₁ := projectPoint (Over.mk a) (f≫x) (𝟙 T) (complexPoint a x f p)
    let q₁ := projectPoint (Over.mk a) (f≫x) (𝟙 T) (complexPoint a x f q)
    have hp : p₀.left=p₁.left := (complexPoint_project a x f p).symm
    have hq : q₀.left=q₁.left := (complexPoint_project a x f q).symm
    calc
      _ = (p*q).left≫pullback.fst a x := complexPoint_project a x f (p*q)
      _ = (p₀*q₀).left := projected_mul (Over.mk a) x f p q
      _ = (p₁*q₁).left := product_congr_left (Over.mk a) hp hq
      _ = _ := (projected_mul (Over.mk a) (f≫x) (𝟙 T)
        (complexPoint a x f p) (complexPoint a x f q)).symm
  · exact (complexPoint a x f (p*q)).w.trans
      (complexPoint a x f p*complexPoint a x f q).w.symm
end LiftOriginalE

variable {A₃₃ A₃ Y₃₃ Y₃:Scheme.{u}} (a₃₃:A₃₃⟶Y₃₃) (a₃:A₃⟶Y₃)
  (forget:Y₃₃⟶Y₃) (u₀:A₃₃⟶A₃) (cart:IsPullback u₀ a₃₃ a₃ forget)
variable {L E C:Type u} [Field L] [Field E] [Field C] (i:L→+*E) (σ:E→+*C)
  (P:Spec (.of E)⟶Y₃₃) (x3:Spec (.of L)⟶Y₃)
  (named:specOf i≫x3=P≫forget)
variable {Z:Type u}

include cart named in
/-- The one existing E-point map, read after the full actual complex
field base change and actual 33-to-3 comparison. -/
def originalInThree
    (qE:Z→(Over.mk (specOf σ)⟶fiber a₃₃ P)) (z:Z):
    Over.mk (𝟙 (Spec (CommRingCat.of C)))⟶fiber a₃ (specOf (σ.comp i)≫x3) :=
  (complexPoint a₃₃ P (specOf σ) (qE z))≫
    (complex a₃₃ a₃ forget u₀ cart i σ P x3 named).hom

include cart named in
@[reassoc] theorem original_full_projection
    (qE:Z→(Over.mk (specOf σ)⟶fiber a₃₃ P)) (z:Z):
    (originalInThree a₃₃ a₃ forget u₀ cart i σ P x3 named qE z).left≫
      pullback.fst a₃ (specOf (σ.comp i)≫x3) =
    (qE z).left≫pullback.fst a₃₃ P≫u₀ :=
  let p := complexPoint a₃₃ P (specOf σ) (qE z)
  let φ := (complex a₃₃ a₃ forget u₀ cart i σ P x3 named).hom
  (Category.assoc p.left φ.left (pullback.fst a₃ (specOf (σ.comp i)≫x3))).trans
    ((congrArg (fun b=>p.left≫b)
      (complex_projection a₃₃ a₃ forget u₀ cart i σ P x3 named)).trans
      ((Category.assoc p.left (pullback.fst a₃₃ (specOf σ≫P)) u₀).symm.trans
        (congrArg (fun b=>b≫u₀) (complexPoint_project a₃₃ P (specOf σ) (qE z)))))

include cart named in
theorem original_full_add [Add Z] [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom]
    (qE:Z→(Over.mk (specOf σ)⟶fiber a₃₃ P))
    (added:∀z w:Z,qE (z+w)=qE z*qE w) (z w:Z):
    originalInThree a₃₃ a₃ forget u₀ cart i σ P x3 named qE (z+w)=
      originalInThree a₃₃ a₃ forget u₀ cart i σ P x3 named qE z *
        originalInThree a₃₃ a₃ forget u₀ cart i σ P x3 named qE w :=
  let embed := complexPoint a₃₃ P (specOf σ)
  let φ := (complex a₃₃ a₃ forget u₀ cart i σ P x3 named).hom
  calc
    _ = (embed (qE z*qE w))≫φ := congrArg (fun b=>embed b≫φ) (added z w)
    _ = (embed (qE z)*embed (qE w))≫φ :=
      congrArg (fun b=>b≫φ) (complexPoint_mul a₃₃ P (specOf σ) (qE z) (qE w))
    _ = _ := complex_points_product a₃₃ a₃ forget u₀ cart i σ P x3 named
      (embed (qE z)) (embed (qE w))

end OriginalRetainedComplexPointFromE318
