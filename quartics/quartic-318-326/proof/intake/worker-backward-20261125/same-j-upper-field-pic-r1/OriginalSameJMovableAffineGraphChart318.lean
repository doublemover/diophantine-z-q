module
public import OriginalCyclicDivisorCartierAllOpenFrames318
public import OriginalCyclicDivisorFieldFibreCartier318
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section
noncomputable section

namespace OriginalSameJMovableAffineGraphChart318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open OriginalCyclicDivisorCartierAllOpenFrames318 (Chart)
open OriginalCyclicDivisorFieldFibreCartier318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {A : CommRingCat.{u}} {E : Type u} [CommRing E]
variable (j : Spec A ⟶ X) [IsOpenImmersion j] (g : A →+* E)
variable (x : A) (hx : g x=0) (δ : A ⧸ J x)
variable (he : RingHom.ker (fibreRead g x hx)=Ideal.span {δ}) (hid : δ*δ=δ)
variable (hg : Function.Surjective g)

abbrev point : Spec (CommRingCat.of E) ⟶ X :=
  Spec.map (CommRingCat.ofHom g) ≫ j

abbrev B := CommRingCat.of (L x δ)
abbrev theta : A ⟶ B x δ := CommRingCat.ofHom (into x δ)
abbrev chartArrow : Spec (B x δ) ⟶ X := Spec.map (theta x δ) ≫ j
abbrev xloc : B x δ := into x δ x
abbrev k : B x δ ⟶ CommRingCat.of E :=
  CommRingCat.ofHom (locRead g x hx δ he)

omit [IsOpenImmersion j] in
theorem samePoint : Spec.map (k g x hx δ he) ≫ chartArrow j x δ = point j g := by
  have hk : theta x δ ≫ k g x hx δ he = CommRingCat.ofHom g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact locRead_input g x hx δ he a
  rw [←Category.assoc,←Spec.map_comp,hk]

include hid in
def cutIso : (L x δ ⧸ Ideal.span {xloc x δ}) ≃+* E :=
  (Ideal.quotEquivOfEq (localized_kernel g x hx δ he hid).symm).trans
    (RingHom.quotientKerEquivOfSurjective (loc_surj g x hx δ he hg))

include hid in
theorem cutIso_read (a : L x δ) :
    cutIso g x hx δ he hid hg (Ideal.Quotient.mk _ a) = locRead g x hx δ he a := by
  simp only [cutIso,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

abbrev D := CommRingCat.of (L x δ ⧸ Ideal.span {xloc x δ})

abbrev quotientArrow : Spec (D x δ) ⟶ Spec (B x δ) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

include hid in
def cutSource : Spec (D x δ) ≅ Spec (CommRingCat.of E) :=
  Scheme.Spec.mapIso (cutIso g x hx δ he hid hg).toCommRingCatIso.symm.op

include hid in
theorem cutSource_read :
    (cutSource g x hx δ he hid hg).hom ≫ Spec.map (k g x hx δ he) =
      quotientArrow x δ := by
  let e := cutIso g x hx δ he hid hg
  have hh : (k g x hx δ he) ≫ e.toCommRingCatIso.inv =
      CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {xloc x δ})) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e.symm (locRead g x hx δ he a) = Ideal.Quotient.mk _ a
    apply e.injective
    exact (e.apply_symm_apply _).trans (cutIso_read g x hx δ he hid hg a).symm
  change Spec.map e.toCommRingCatIso.inv ≫ Spec.map (k g x hx δ he) = _
  rw [←Spec.map_comp,hh]

include hid in
/-- Pulling back the actual whole affine graph to its basic open gives
its literal principal quotient, preserving all coordinates of g. -/
theorem square :
    IsPullback (quotientArrow x δ) (cutSource g x hx δ he hid hg).hom
      (chartArrow j x δ) (point j g) := by
  apply IsPullback.of_vert_isIso_mono
  refine ⟨?_⟩
  rw [←cutSource_read g x hx δ he hid hg,Category.assoc,samePoint j g x hx δ he]

theorem regular_local (hr : ∀ a : A, a*x=0 → a=0) :
    ∀ a : L x δ, a*xloc x δ=0 → a=0 := by
  have hx' : x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact hr a (by simpa only [mul_comm] using ha)
  have hloc : xloc x δ ∈ nonZeroDivisors (L x δ) :=
    IsLocalization.nonZeroDivisors_le_comap
      (M:=Submonoid.powers (retainedDenominator x δ)) (S:=L x δ) hx'
  intro a ha
  rw [mem_nonZeroDivisors_iff_left] at hloc
  exact hloc a (by simpa only [mul_comm] using ha)

include hid in
/-- The actual whole affine graph has a regular closed chart on the
same scheme, starting from its own named étale fibre factor. -/
def chart (hr : ∀ a : A, a*x=0 → a=0) : Chart (point j g) :=
  ⟨B x δ,chartArrow j x δ,inferInstance,xloc x δ,
    (cutSource g x hx δ he hid hg).hom,square j g x hx δ he hid hg,regular_local x δ hr⟩

include hid in
theorem meets (hr : ∀ a : A, a*x=0 → a=0) (a : Spec (CommRingCat.of E)) :
    point j g a ∈ (chart j g x hx δ he hid hg hr).V.1 := by
  change point j g a ∈ chartArrow j x δ ''ᵁ ⊤
  have h := congrArg (fun f : Spec (CommRingCat.of E) ⟶ X => f a)
    (samePoint j g x hx δ he)
  refine ⟨Spec.map (k g x hx δ he) a,Set.mem_univ _,?_⟩
  exact (Scheme.Hom.comp_apply (Spec.map (k g x hx δ he)) (chartArrow j x δ) a).symm.trans h

end OriginalSameJMovableAffineGraphChart318

#print axioms OriginalSameJMovableAffineGraphChart318.square
#print axioms OriginalSameJMovableAffineGraphChart318.meets
