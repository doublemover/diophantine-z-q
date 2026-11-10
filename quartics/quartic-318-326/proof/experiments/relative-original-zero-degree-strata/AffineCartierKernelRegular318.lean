module
public import AffineZeroKernelRestriction318
public import OriginalAffineRegularOpenPullback318
public import OriginalRegularClosedCharts318
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace AffineCartierKernelRegular318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318 AffineZeroKernelRestriction318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Flat coefficient change preserves the ACTUAL nonzerodivisor. -/
lemma regular_map {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.Flat) (c : A) (hc : ∀ a : A,a*c=0 → a=0) :
    ∀ b : B,b*f c=0 → b=0 := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hn : c∈nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact hc a (by simpa only [mul_comm] using ha)
  intro b hb
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M:=B) hn
  change f c*b=f c*0
  simpa only [mul_comm,mul_zero] using hb

/-- Restriction between genuine affine opens is flat, obtained from the
identity scheme morphism's actual appLE, not assumed for a zero family. -/
lemma restriction_flat {X : Scheme.{u}} (V W : X.affineOpens) (h : W≤V) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have hf := (𝟙 X).flat_appLE V.2 W.2 h
  simpa only [Scheme.Hom.appLE,Scheme.Hom.id_app,Category.id_comp] using hf

variable {Z X : Scheme.{u}} (p : Z ⟶ X)
/-- Literal zero-kernel membership together with regularity in the actual
section ring. This is stronger than information about the zero support. -/
def HasRegularKernel (V : X.Opens) : Prop := ∃ a : Γ(X,V),
  a∈RingHom.ker (p.app V).hom ∧ ∀ b : Γ(X,V),b*a=0 → b=0

variable [QuasiCompact p] (A : CommRingCat.{u}) (j : Spec A ⟶ X)
  [IsOpenImmersion j] (c : A)
  (z : Spec (CommRingCat.of (A⧸Ideal.span {c})) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
  (hc : ∀ a : A,a*c=0 → a=0)

/-- Every actual affine subopen of a proved Cartier chart contains a
nonzerodivisor in the SAME global zero-map kernel, with the coefficient
produced by its exact original section restriction. -/
lemma on_affine_subopen (V : X.affineOpens) (hV : V≤chartOpen A j) :
    HasRegularKernel p V.1 := by
  let f := (restrictedCoefficient A j V hV).hom
  have hf : f.Flat := (RingHom.Flat.of_bijective (coefficient_bijective A j)).comp
    (restriction_flat (chartOpen A j) V hV)
  refine ⟨f c,?_,regular_map f hf c hc⟩
  rw [restricted_kernel A (Ideal.span {c}) p j z hs V hV]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span (Set.mem_singleton c))

/-- A regular element of the actual principal section ideal makes its
original section coefficient regular. No unit or cancellation premise is
assumed: divisibility follows from literal ideal membership. -/
lemma regular_of_mem_principal {A : Type u} [CommRing A] (c d : A)
    (hd : ∀ a : A,a*d=0 → a=0) (hm : d∈Ideal.span ({c}:Set A)) :
    ∀ a : A,a*c=0 → a=0 := by
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp hm
  intro a ha
  apply hd a
  rw [← hb]
  calc
    a*(b*c)=b*(a*c) := by ring
    _=0 := by rw [ha,mul_zero]
end AffineCartierKernelRegular318
