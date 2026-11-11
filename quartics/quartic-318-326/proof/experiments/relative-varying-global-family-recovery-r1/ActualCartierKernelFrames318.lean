module
public import AffineCartierKernelRegular318
public import ActualClosedIdealModule318
public section
noncomputable section
namespace ActualCartierKernelFrames318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineQuotientKernelSections318 AffineZeroKernelRestriction318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [QuasiCompact p]
  (A : CommRingCat.{u}) (j : Spec A ⟶ X) [IsOpenImmersion j] (c : A)
  (z : Spec (CommRingCat.of (A ⧸ Ideal.span {c})) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j p)
  (hc : ∀ a : A,a*c=0 → a=0)
  (V : X.affineOpens) (hV : V≤chartOpen A j)
local notation "R" => Γ(X,V.1)
local notation "E" => SheafOfModules.evaluation X.ringCatSheaf (op V.1)
local notation "K" => LinearMap.ker (E.map (ActualClosedIdealModule318.structure p)).hom

/-- The literal Cartier equation on this ORIGINAL affine subopen. -/
@[expose] def equation : R := restrictedCoefficient A j V hV c

lemma kernel_eq : K=Ideal.span ({equation A j c V hV} : Set R) := by
  rw [ActualClosedIdealModule318.section_kernel,
    restricted_kernel A (Ideal.span {c}) p j z hs V hV]
  simp only [Ideal.map_span,Set.image_singleton,equation]

lemma regular : ∀ a : R,a*equation A j c V hV=0 → a=0 := by
  have hf : (restrictedCoefficient A j V hV).hom.Flat :=
    (RingHom.Flat.of_bijective (coefficient_bijective A j)).comp
      (AffineCartierKernelRegular318.restriction_flat (chartOpen A j) V hV)
  exact AffineCartierKernelRegular318.regular_map _ hf c hc

/-- Multiplication into the ACTUAL linear kernel, with its actual section
ring and scalar action. This never promotes IdealSheafData into a module. -/
@[expose] def multiply : R →ₗ[R] K where
  toFun a := ⟨a*equation A j c V hV,by
    rw [kernel_eq p A j c z hs V hV]
    exact Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩⟩
  map_add' a b := Subtype.ext (add_mul a b _)
  map_smul' a b := Subtype.ext (mul_assoc a b _)

lemma bijective : Function.Bijective (multiply p A j c z hs V hV) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply regular A j c hc V hV
    rw [sub_mul]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  · intro x
    have hx : (x:R)∈Ideal.span ({equation A j c V hV} : Set R) := by
      rw [← kernel_eq p A j c z hs V hV]
      exact x.property
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨a,Subtype.ext ha⟩

/-- A genuine rank-one frame for the ACTUAL kernel module sections on
EVERY affine subopen of the original Cartier chart. Its inclusion formula
below fixes the frame, not merely its abstract rank. -/
@[expose] def frame : R ≃ₗ[R] Γ(ActualClosedIdealModule318.object p,V.1) :=
  (LinearEquiv.ofBijective (multiply p A j c z hs V hV)
    (bijective p A j c z hs hc V hV)).trans
      (ActualClosedIdealModule318.sectionsIso p V.1).toLinearEquiv.symm

lemma frame_inclusion (a : R) :
    (ActualClosedIdealModule318.inclusion p).app V.1
      (frame p A j c z hs hc V hV a)=a*equation A j c V hV := by
  have he := ActualClosedIdealModule318.sectionsIso_inv_inclusion p V.1
  have ha := congrArg (fun k => k (multiply p A j c z hs V hV a)) he
  exact ha
end ActualCartierKernelFrames318
