module
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section
noncomputable section

namespace OriginalRetainedComplexZeroByPasting318

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

abbrev fiber {A Y S : Scheme.{u}} (a : A ⟶ Y) (x : S ⟶ Y) :=
  (Over.pullback x).obj (Over.mk a)

/-- The literal two-stage field specialization, used when a chosen
chart is first formed on the arithmetic fibre and then moved to σ. -/
def iter {A Y V S : Scheme.{u}} (a : A ⟶ Y) (x : V ⟶ Y) (f : S ⟶ V) :
    fiber (pullback.snd a x) f ≅ fiber a (f ≫ x) :=
  let H := (IsPullback.of_hasPullback (pullback.snd a x) f).paste_horiz
    (IsPullback.of_hasPullback a x)
  Over.isoMk H.isoPullback H.isoPullback_hom_snd

@[reassoc] theorem iter_read {A Y V S : Scheme.{u}}
    (a : A ⟶ Y) (x : V ⟶ Y) (f : S ⟶ V) :
    (iter a x f).hom.left ≫ pullback.fst a (f ≫ x) =
      pullback.fst (pullback.snd a x) f ≫ pullback.fst a x :=
  ((IsPullback.of_hasPullback (pullback.snd a x) f).paste_horiz
    (IsPullback.of_hasPullback a x)).isoPullback_hom_fst

def specOf {K M : Type u} [CommRing K] [CommRing M] (e : K →+* M) :
    Spec (.of M) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom e)

theorem spec_comp {K L E : Type u} [CommRing K] [CommRing L] [CommRing E]
    (i : K →+* L) (σ : L →+* E) :
    specOf σ ≫ specOf i = specOf (σ.comp i) :=
  (Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom σ)).symm

/-- The geometric unit of this actual slice group, not an independently selected point. -/
def zero {S : Scheme.{u}} (A : Over S) [MonObj A] : S ⟶ A.left :=
  (MonObj.one (X := A)).left

theorem zero_over {S : Scheme.{u}} (A : Over S) [MonObj A] :
    zero A ≫ A.hom = 𝟙 S :=
  Over.w (MonObj.one (X := A))

/-- Canonically pulled-back group unit, read on the original total space. -/
theorem zero_fst {S T : Scheme.{u}} (A : Over S) [MonObj A] (p : T ⟶ S) :
    zero ((Over.pullback p).obj A) ≫ pullback.fst A.hom p = p ≫ zero A := by
  let c : T ⟶ pullback (𝟙 S) p := (Functor.LaxMonoidal.ε (Over.pullback p)).left
  have cs : c ≫ pullback.snd (𝟙 S) p = 𝟙 T := by
    change (Functor.LaxMonoidal.ε (Over.pullback p)).left ≫
      pullback.snd (𝟙 S) p = 𝟙 T
    simp only [Over.ε_pullback_left, IsIso.inv_hom_id, Over.tensorUnit_left]
  have cf : c ≫ pullback.fst (𝟙 S) p = p := by
    calc
      _ = c ≫ (pullback.fst (𝟙 S) p ≫ 𝟙 S) := by rw [Category.comp_id]
      _ = c ≫ (pullback.snd (𝟙 S) p ≫ p) := by rw [pullback.condition]
      _ = p := by rw [← Category.assoc, cs, Category.id_comp]
  have hm : ((Over.pullback p).map (MonObj.one (X := A))).left ≫
      pullback.fst A.hom p = pullback.fst (𝟙 S) p ≫ zero A := by
    simp only [Over.pullback_map_left, pullback.lift_fst, Over.tensorUnit_hom, zero]
  change (c ≫ ((Over.pullback p).map (MonObj.one (X := A))).left) ≫
    pullback.fst A.hom p = p ≫ zero A
  rw [Category.assoc, hm, ← Category.assoc, cf]

theorem zero_snd {S T : Scheme.{u}} (A : Over S) [MonObj A] (p : T ⟶ S) :
    zero ((Over.pullback p).obj A) ≫ pullback.snd A.hom p = 𝟙 T :=
  zero_over ((Over.pullback p).obj A)

variable {A₃₃ A₃ Y₃₃ Y₃ : Scheme.{u}}
variable (a₃₃ : A₃₃ ⟶ Y₃₃) (a₃ : A₃ ⟶ Y₃) (forget : Y₃₃ ⟶ Y₃) (u₀ : A₃₃ ⟶ A₃)
    (cart : IsPullback u₀ a₃₃ a₃ forget)

/-- The representable universal forget square, in direction 33 to 3. -/
def universal : Over.mk a₃₃ ≅ fiber a₃ forget :=
  Over.isoMk cart.isoPullback cart.isoPullback_hom_snd

/-- This is the sole group-theoretic compatibility needed: the actual universal
forget isomorphism is a homomorphism to the canonically pulled-back group.
The equality of selected origins is a conclusion, not another input. -/
theorem total_origin [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom] :
    zero (Over.mk a₃₃) ≫ u₀ = forget ≫ zero (Over.mk a₃) := by
  have hu : (universal a₃₃ a₃ forget u₀ cart).hom.left ≫ pullback.fst a₃ forget = u₀ :=
    cart.isoPullback_hom_fst
  have h := congrArg (fun f : (𝟙_ (Over Y₃₃)) ⟶ fiber a₃ forget =>
      f.left ≫ pullback.fst a₃ forget)
    (IsMonHom.one_hom (universal a₃₃ a₃ forget u₀ cart).hom)
  change (zero (Over.mk a₃₃) ≫ (universal a₃₃ a₃ forget u₀ cart).hom.left) ≫
    pullback.fst a₃ forget = zero (fiber a₃ forget) ≫ pullback.fst a₃ forget at h
  rw [Category.assoc, hu] at h
  exact h.trans (zero_fst (Over.mk a₃) forget)

variable {L E C : Type u} [Field L] [Field E] [Field C]
variable (i : L →+* E) (σ : E →+* C)
variable (x : Spec (.of E) ⟶ Y₃₃) (xL : Spec (.of L) ⟶ Y₃)
    (named : specOf i ≫ xL = x ≫ forget)

include named in
theorem point_three_sigma :
    (specOf σ ≫ x) ≫ forget = specOf (σ.comp i) ≫ xL := by
  calc
    _ = specOf σ ≫ (x ≫ forget) := Category.assoc _ _ _
    _ = specOf σ ≫ (specOf i ≫ xL) := by rw [named]
    _ = (specOf σ ≫ specOf i) ≫ xL := (Category.assoc _ _ _).symm
    _ = _ := by rw [spec_comp]

include cart named in
/-- This uses the actual universal arrow u₀ and literal complex embeddings,
not a separately chosen point at the same T. -/
theorem complex_cart :
    IsPullback (pullback.fst a₃₃ (specOf σ ≫ x) ≫ u₀)
      (pullback.snd a₃₃ (specOf σ ≫ x)) a₃ (specOf (σ.comp i) ≫ xL) := by
  rw [← point_three_sigma forget i σ x xL named]
  exact (IsPullback.of_hasPullback a₃₃ (specOf σ ≫ x)).paste_horiz cart

include cart named in
def complex : fiber a₃₃ (specOf σ ≫ x) ≅ fiber a₃ (specOf (σ.comp i) ≫ xL) :=
  let H := complex_cart a₃₃ a₃ forget u₀ cart i σ x xL named
  Over.isoMk H.isoPullback H.isoPullback_hom_snd

theorem complex_projection :
    (complex a₃₃ a₃ forget u₀ cart i σ x xL named).hom.left ≫
        pullback.fst a₃ (specOf (σ.comp i) ≫ xL) =
    pullback.fst a₃₃ (specOf σ ≫ x) ≫ u₀ :=
  (complex_cart a₃₃ a₃ forget u₀ cart i σ x xL named).isoPullback_hom_fst

/-- The literal retained complex 33-to-3 map takes the actual complex
unit to the original level-three unit, prior to all Hodge-chart choices. -/
theorem complex_selected_zero [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom] :
    zero (fiber a₃₃ (specOf σ ≫ x)) ≫ (complex a₃₃ a₃ forget u₀ cart i σ x xL named).hom.left =
      zero (fiber a₃ (specOf (σ.comp i) ≫ xL)) := by
  let p := specOf σ ≫ x
  let q := specOf (σ.comp i) ≫ xL
  let f := (complex a₃₃ a₃ forget u₀ cart i σ x xL named).hom
  have hf : f.left ≫ pullback.fst a₃ q = pullback.fst a₃₃ p ≫ u₀ :=
    complex_projection a₃₃ a₃ forget u₀ cart i σ x xL named
  have hname : p ≫ forget = q := point_three_sigma forget i σ x xL named
  change zero (fiber a₃₃ p) ≫ f.left = zero (fiber a₃ q)
  apply pullback.hom_ext
  · change (zero (fiber a₃₃ p) ≫ f.left) ≫ pullback.fst a₃ q =
      zero (fiber a₃ q) ≫ pullback.fst a₃ q
    calc
      _ = zero (fiber a₃₃ p) ≫ (pullback.fst a₃₃ p ≫ u₀) :=
        (Category.assoc _ _ _).trans (congrArg (fun r => zero (fiber a₃₃ p) ≫ r) hf)
      _ = (zero (fiber a₃₃ p) ≫ pullback.fst a₃₃ p) ≫ u₀ :=
        (Category.assoc _ _ _).symm
      _ = (p ≫ zero (Over.mk a₃₃)) ≫ u₀ :=
        congrArg (fun r : Spec (.of C) ⟶ A₃₃ => r ≫ u₀) (zero_fst (Over.mk a₃₃) p)
      _ = p ≫ (zero (Over.mk a₃₃) ≫ u₀) := Category.assoc _ _ _
      _ = p ≫ (forget ≫ zero (Over.mk a₃)) := by
        rw [total_origin a₃₃ a₃ forget u₀ cart]
      _ = (p ≫ forget) ≫ zero (Over.mk a₃) := (Category.assoc _ _ _).symm
      _ = q ≫ zero (Over.mk a₃) := by rw [hname]
      _ = _ := (zero_fst (Over.mk a₃) q).symm
  · change (zero (fiber a₃₃ p) ≫ f.left) ≫ pullback.snd a₃ q =
      zero (fiber a₃ q) ≫ pullback.snd a₃ q
    have hbase : f.left ≫ pullback.snd a₃ q = pullback.snd a₃₃ p := Over.w f
    calc
      _ = zero (fiber a₃₃ p) ≫ pullback.snd a₃₃ p :=
        (Category.assoc _ _ _).trans (congrArg (fun r => zero (fiber a₃₃ p) ≫ r) hbase)
      _ = 𝟙 _ := zero_snd (Over.mk a₃₃) p
      _ = _ := (zero_snd (Over.mk a₃) q).symm

/-- Read actual regular functions at a pointed scheme arrow on the chosen
source open and target open. Fixed domain opens avoid rewriting a pullback
open inside its own section type. -/
theorem app_at_same_origin {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (e : S ⟶ X) (e' : S ⟶ Y) (h : e ≫ f = e')
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (hE : (⊤ : S.Opens) ≤ e ⁻¹ᵁ V) :
    ∃ hE' : (⊤ : S.Opens) ≤ e' ⁻¹ᵁ U,
      f.appLE U V hV ≫ e.appLE V ⊤ hE = e'.appLE U ⊤ hE' := by
  subst e'
  let hT := hE.trans ((Opens.map e.base).map (homOfLE hV)).le
  exact ⟨hT, Scheme.Hom.appLE_comp_appLE e f U V ⊤ hV hE⟩

/-- Apply the original marked zero, without choosing a substitute chart.
The two opens are exactly the caller's original charts. This is an actual
augmentation equality; differential reads still use Kähler naturality. -/
theorem complex_selected_functions [MonObj (Over.mk a₃₃)] [MonObj (Over.mk a₃)]
    [IsMonHom (universal a₃₃ a₃ forget u₀ cart).hom] :
    let F33 := fiber a₃₃ (specOf σ ≫ x)
    let F3 := fiber a₃ (specOf (σ.comp i) ≫ xL)
    let f := (complex a₃₃ a₃ forget u₀ cart i σ x xL named).hom.left
    ∀ (U : F3.left.Opens) (V : F33.left.Opens) (hV : V ≤ f ⁻¹ᵁ U)
      (hE : (⊤ : (Spec (.of C)).Opens) ≤ zero F33 ⁻¹ᵁ V),
      ∃ hE' : (⊤ : (Spec (.of C)).Opens) ≤ zero F3 ⁻¹ᵁ U,
        f.appLE U V hV ≫ (zero F33).appLE V ⊤ hE =
          (zero F3).appLE U ⊤ hE' := by
  dsimp only
  intro U V hV hE
  exact app_at_same_origin _ _ _ (complex_selected_zero a₃₃ a₃ forget u₀ cart i σ x xL named)
    U V hV hE

end OriginalRetainedComplexZeroByPasting318

#print axioms OriginalRetainedComplexZeroByPasting318.iter_read
#print axioms OriginalRetainedComplexZeroByPasting318.complex_projection
#print axioms OriginalRetainedComplexZeroByPasting318.total_origin
#print axioms OriginalRetainedComplexZeroByPasting318.complex_selected_zero
#print axioms OriginalRetainedComplexZeroByPasting318.complex_selected_functions
