module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorCartierAffineFrames318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Algebra

variable {D₀ A₀ : Type u} [CommRing D₀] [CommRing A₀]

/-- Exact Spec/Γ kernel in the literal affine ring. This is the audited
r45 generic lemma, isolated from the unavailable modular-source object. -/
theorem spec_kernel (v : A₀ →+* D₀) :
    ((Spec.map (CommRingCat.ofHom v)).ker.ideal
      ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of A₀))⟩).comap
        (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom = RingHom.ker v := by
  rw [Scheme.Hom.ker_apply]
  ext a
  change (Spec.map (CommRingCat.ofHom v)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a) = 0 ↔ v a = 0
  have he := congrArg (fun k => k a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom v))
  change (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv (v a) =
    (Spec.map (CommRingCat.ofHom v)).appTop ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv a) at he
  rw [← he,map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of D₀)).inv).1]

abbrev fixedComap (f : A₀ →+* D₀) (I : Ideal D₀) : Ideal A₀ := I.comap f

variable {B : Type u} [CommRing B] (I : Ideal B) (c : B)
variable (hI : I = Ideal.span {c}) (hc : ∀ x : B, x*c=0 → x=0)

/-- Frame of the actual ideal subtype, retaining its inclusion. -/
def multiply : B →ₗ[B] I where
  toFun a := ⟨a*c,by
    rw [hI]
    exact Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩⟩
  map_add' a b := Subtype.ext (add_mul a b _)
  map_smul' a b := Subtype.ext (mul_assoc a b _)

include hc in
theorem bijective : Function.Bijective (multiply I c hI) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply hc
    rw [sub_mul]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  · intro x
    have hx : (x : B) ∈ Ideal.span {c} := hI ▸ x.property
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨a,Subtype.ext ha⟩

def basis : B ≃ₗ[B] I := LinearEquiv.ofBijective (multiply I c hI) (bijective I c hI hc)

theorem basis_inclusion (a : B) : (basis I c hI hc a : B) = a*c := rfl

end Algebra

section ActualChart

variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
variable (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j] (c : A)
variable (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z)
variable (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
variable (hc : ∀ a : A, a*c=0 → a=0)

abbrev chartOpen : X.affineOpens :=
  ⟨j ''ᵁ ⊤,(isAffineOpen_top (Spec A)).image_of_isOpenImmersion j⟩

def coordinateIso : A ≅ Γ(X,(chartOpen A j).1) :=
  (Scheme.ΓSpecIso A).symm ≪≫ (j.appIso ⊤).symm

include hs in
/-- The actual old quotient square computes the full old kernel. -/
theorem chart_kernel :
    (p.ker.ideal (chartOpen A j)).comap (coordinateIso A j).hom.hom = Ideal.span {c} := by
  let q : A →+* A ⧸ Ideal.span {c} := Ideal.Quotient.mk (Ideal.span {c})
  let U : (Spec A).affineOpens := ⟨⊤,isAffineOpen_top (Spec A)⟩
  let fromRing : A →+* Γ(Spec A,U.1) := (Scheme.ΓSpecIso A).inv.hom
  let toChart : Γ(Spec A,U.1) →+* Γ(X,(chartOpen A j).1) :=
    (j.appIso U.1).inv.hom
  let topIdeal : Ideal Γ(Spec A,U.1) :=
    fixedComap (A₀:=Γ(Spec A,U.1)) (D₀:=Γ(X,(chartOpen A j).1))
      toChart (p.ker.ideal (chartOpen A j))
  let intoRing : Ideal Γ(Spec A,U.1) → Ideal A :=
    fixedComap (A₀:=A) (D₀:=Γ(Spec A,U.1)) fromRing
  have read : (Spec.map (CommRingCat.ofHom q)).ker.ideal U = topIdeal :=
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion p
      (Spec.map (CommRingCat.ofHom q)) z j hs U
  calc
    _ = intoRing topIdeal := rfl
    _ = intoRing ((Spec.map (CommRingCat.ofHom q)).ker.ideal U) :=
      congrArg intoRing read.symm
    _ = RingHom.ker q := spec_kernel q
    _ = _ := by
      ext a
      exact Ideal.Quotient.eq_zero_iff_mem

variable (V : X.affineOpens) (hV : V ≤ chartOpen A j)

def restricted : A ⟶ Γ(X,V.1) :=
  (coordinateIso A j).hom ≫ X.presheaf.map (homOfLE hV).op

def equation : Γ(X,V.1) := restricted A j V hV c

include hs in
/-- Every affine subopen sees the same ideal, not just the top chart. -/
theorem ideal_eq : p.ker.ideal V = Ideal.span {equation A j c V hV} := by
  have surj : Function.Surjective (coordinateIso A j).hom :=
    (ConcreteCategory.bijective_of_isIso (coordinateIso A j).hom).2
  have on_top : p.ker.ideal (chartOpen A j) =
      (Ideal.span {c}).map (coordinateIso A j).hom.hom := by
    rw [← chart_kernel p A j c z hs]
    exact (Ideal.map_comap_of_surjective _ surj _).symm
  calc
    p.ker.ideal V = (p.ker.ideal (chartOpen A j)).map
        (X.presheaf.map (homOfLE hV).op).hom := (p.ker.map_ideal hV).symm
    _ = (Ideal.span {c}).map (restricted A j V hV).hom := by
      rw [on_top,Ideal.map_map]
      rfl
    _ = Ideal.span {equation A j c V hV} := by
      rw [Ideal.map_span,Set.image_singleton]
      rfl

include hc in
/-- Actual open restrictions preserve regularity by flatness, not by
a reducedness/domain test on the new coefficient ring. -/
theorem equation_regular : ∀ a : Γ(X,V.1), a*equation A j c V hV=0 → a=0 := by
  let r := (restricted A j V hV).hom
  have path : (X.presheaf.map (show V.1 ⟶ (chartOpen A j).1 from homOfLE hV).op).hom.Flat := by
    have h := Scheme.Hom.flat_appLE (𝟙 X : X ⟶ X) (chartOpen A j).2 V.2 hV
    simpa only [Scheme.Hom.appLE,Scheme.Hom.id_app,Category.id_comp] using h
  have hΓ : (coordinateIso A j).hom.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (coordinateIso A j).hom)
  have hr : r.Flat := hΓ.comp path
  let : Algebra A Γ(X,V.1) := r.toAlgebra
  let : Module.Flat A Γ(X,V.1) := hr
  have hn : c ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact hc a (by simpa only [mul_comm] using ha)
  intro a ha
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M:=Γ(X,V.1)) hn
  change r c*a = r c*0
  have hz : a*r c=0 := ha
  exact (mul_comm _ _).trans (hz.trans (mul_zero _).symm)

/-- Frame of the actual global ideal's sections on a genuine affine
subopen of a genuine Cartier chart. Its inclusion is multiplication. -/
def frame : Γ(X,V.1) ≃ₗ[Γ(X,V.1)] p.ker.ideal V :=
  basis (p.ker.ideal V) (equation A j c V hV)
    (ideal_eq p A j c z hs V hV) (equation_regular A j c hc V hV)

theorem frame_inclusion (a : Γ(X,V.1)) :
    (frame p A j c z hs hc V hV a : Γ(X,V.1)) = a*equation A j c V hV := rfl

variable (W : X.affineOpens) (hWV : W ≤ V)

/-- Restrictions of the chosen equation are the actual ring maps of
the original structure sheaf. -/
theorem equation_restrict :
    X.presheaf.map (homOfLE hWV).op (equation A j c V hV) =
      equation A j c W (hWV.trans hV) := by
  have he : restricted A j V hV ≫ X.presheaf.map (homOfLE hWV).op =
      restricted A j W (hWV.trans hV) := by
    unfold restricted
    rw [Category.assoc,←Functor.map_comp]
    rfl
  exact congrArg (fun f => f c) he

theorem frame_restrict (a : Γ(X,V.1)) :
    X.presheaf.map (homOfLE hWV).op (frame p A j c z hs hc V hV a : Γ(X,V.1)) =
      (frame p A j c z hs hc W (hWV.trans hV)
        (X.presheaf.map (homOfLE hWV).op a) : Γ(X,W.1)) := by
  rw [frame_inclusion,map_mul,equation_restrict,frame_inclusion]

end ActualChart

end OriginalCyclicDivisorCartierAffineFrames318

#print axioms OriginalCyclicDivisorCartierAffineFrames318.ideal_eq
#print axioms OriginalCyclicDivisorCartierAffineFrames318.frame_restrict
