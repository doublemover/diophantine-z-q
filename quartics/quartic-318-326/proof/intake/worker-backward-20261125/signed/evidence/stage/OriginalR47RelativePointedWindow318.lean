module
public import OriginalR47TraitRoundKernel318
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section

namespace OriginalR47RelativePointedWindow318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The actual relative pointed site, retaining both scheme maps and
their common base.  Do not replace it by an abstract ring isomorphism
or an absolute-regularity statement. -/
structure Window {X T S : Scheme.{u}} (f : X ⟶ S) (x : X) (t : T ⟶ S) where
  U : Scheme.{u}
  w : U
  e : U ⟶ X
  g : U ⟶ T
  [eFlat : Flat e]
  [eUnram : FormallyUnramified e]
  [eFinite : LocallyOfFiniteType e]
  [gFlat : Flat g]
  [gUnram : FormallyUnramified g]
  [gFinite : LocallyOfFiniteType g]
  point : e w = x
  over : e ≫ f = g ≫ t

attribute [instance] Window.eFlat Window.eUnram Window.eFinite
  Window.gFlat Window.gUnram Window.gFinite

variable {X Y T S : Scheme.{u}} {f : X ⟶ S} {x : X} {t : T ⟶ S}

/-- The centre-free interchange may restrict only the *old* arrow.
The target point on the exact literal node/line chart is unchanged,
so the same unit axis or thin-origin test is preserved. -/
theorem pull_open (P : Window f x t) (k : Y ⟶ X) [IsOpenImmersion k]
    (y : Y) (hy : k y = x) :
    ∃ Q : Window (k ≫ f) y t, Q.g Q.w = P.g P.w := by
  let L := IsPullback.of_hasPullback P.e k
  obtain ⟨z,h₁,h₂⟩ := Scheme.exists_preimage_of_isPullback L P.w y
    (P.point.trans hy.symm)
  let j := pullback.fst P.e k
  let a := pullback.snd P.e k
  let : IsOpenImmersion j := MorphismProperty.pullback_fst P.e k
    (inferInstance : IsOpenImmersion k)
  let : Flat a := MorphismProperty.pullback_snd P.e k P.eFlat
  let : FormallyUnramified a := MorphismProperty.pullback_snd P.e k P.eUnram
  let : LocallyOfFiniteType a := MorphismProperty.pullback_snd P.e k P.eFinite
  have unramJ : FormallyUnramified j := inferInstance
  have unramG : FormallyUnramified (j ≫ P.g) :=
    MorphismProperty.comp_mem (@FormallyUnramified) j P.g unramJ P.gUnram
  have over : a ≫ (k ≫ f) = (j ≫ P.g) ≫ t := by
    change (pullback.snd P.e k) ≫ k ≫ f = (pullback.fst P.e k ≫ P.g) ≫ t
    rw [← pullback.condition_assoc, Category.assoc, ← P.over]
  let Q : Window (k ≫ f) y t := {
    U := pullback P.e k
    w := z
    e := a
    g := j ≫ P.g
    eFlat := inferInstance
    eUnram := inferInstance
    eFinite := inferInstance
    gFlat := inferInstance
    gUnram := unramG
    gFinite := inferInstance
    point := h₂
    over := over
  }
  exact ⟨Q,(Scheme.Hom.comp_apply j P.g z).trans (congrArg P.g h₁)⟩

/-- Compose only the chart inclusion with the original open arrow. The
literal model, point and its coefficients are all definitionally the
same. -/
@[expose] def push_open {f' : Y ⟶ S} {y : Y} (P : Window f' y t)
    (j : Y ⟶ X) [IsOpenImmersion j] (h : j ≫ f = f') :
    Window f (j y) t where
  U := P.U
  w := P.w
  e := P.e ≫ j
  g := P.g
  eFlat := inferInstance
  eUnram := MorphismProperty.comp_mem (@FormallyUnramified) P.e j P.eUnram inferInstance
  eFinite := inferInstance
  gFlat := P.gFlat
  gUnram := P.gUnram
  gFinite := P.gFinite
  point := by rw [Scheme.Hom.comp_apply, P.point]
  over := by rw [Category.assoc, h, P.over]

end OriginalR47RelativePointedWindow318

#print axioms OriginalR47RelativePointedWindow318.pull_open
#print axioms OriginalR47RelativePointedWindow318.push_open
