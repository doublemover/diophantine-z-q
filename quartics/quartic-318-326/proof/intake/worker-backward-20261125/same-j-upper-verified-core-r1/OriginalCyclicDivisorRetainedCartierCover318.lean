module
public import OriginalCyclicDivisorPositiveCartierModule318
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorRetainedCartierCover318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open OriginalCyclicDivisorCartierAllOpenFrames318 (Chart)
open OriginalCyclicDivisorPositiveCartierModule318 (Sec canon frame canonical_affine)
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]

abbrev outside : X.Opens :=
  ⟨(Set.range p)ᶜ,p.isClosedEmbedding.isClosed_range.isOpen_compl⟩

omit [IsClosedImmersion p] in
/-- If an actual open avoids the actual closed map, its actual product
with the entire closed scheme is empty; this is not a support reduction. -/
theorem empty_pullback {A : CommRingCat.{u}} (j : Spec A ⟶ X)
    (off : ∀ y : Spec A, j y ∉ Set.range p) :
    IsEmpty ↥(pullback (C:=Scheme.{u}) j p) := by
  refine ⟨fun x=>?_⟩
  apply off (pullback.fst j p x)
  refine ⟨pullback.snd j p x,?_⟩
  have w := congrArg (fun f : pullback j p ⟶ X => f x) (pullback.condition (f:=j) (g:=p))
  simpa only [Scheme.Hom.comp_apply] using w.symm

/-- Literal equation 1 on the actual complementary affine. The
quotient by (1) and the original pullback are both genuinely initial,
so their unique comparison preserves the two named arrows. -/
def empty_chart {A : CommRingCat.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
    (off : ∀ y : Spec A, j y ∉ Set.range p) : Chart p := by
  let d : Ideal A := Ideal.span ({1} : Set A)
  let B := CommRingCat.of (A ⧸ d)
  let E := Spec B
  let q : E ⟶ Spec A := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk d))
  let : Subsingleton (A ⧸ d) :=
    (Ideal.Quotient.subsingleton_iff (I:=d)).mpr Ideal.span_singleton_one
  let : IsEmpty ↥E := inferInstanceAs (IsEmpty (PrimeSpectrum (A ⧸ d)))
  let : IsEmpty ↥(pullback (C:=Scheme.{u}) j p) := empty_pullback p j off
  let ei : IsInitial E := isInitialOfIsEmpty
  let e : E ≅ pullback j p := ei.uniqueUpToIso isInitialOfIsEmpty
  let u : E ⟶ Z := e.hom ≫ pullback.snd j p
  have square : IsPullback q u j p := by
    apply IsPullback.of_iso_pullback (i:=e)
    · exact ⟨ei.hom_ext _ _⟩
    · exact ei.hom_ext _ _
    · rfl
  exact ⟨A,j,inferInstance,1,u,square,fun a ha=>(mul_one a).symm.trans ha⟩

theorem empty_at {x : X} (off : x ∉ Set.range p) :
    ∃ Q : Chart p, x∈Q.V.1 := by
  obtain ⟨U,hU,hx,hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ outside p from off)
  let j : Spec Γ(X,U) ⟶ X := hU.fromSpec
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have read (y : Spec Γ(X,U)) : j y∉Set.range p := by
    apply hsub
    change j y ∈ (U : Set X)
    have hRange : Set.range j = (U : Set X) := hU.range_fromSpec
    exact hRange ▸ (show j y ∈ Set.range j from ⟨y,rfl⟩)
  refine ⟨empty_chart p j read,?_⟩
  change x∈j ''ᵁ ⊤
  have hit : x ∈ Set.range j := by
    rw [show (Set.range j : Set X)=(U:Set X) from hU.range_fromSpec]
    exact hx
  obtain ⟨y,hy⟩ := hit
  exact ⟨y,Set.mem_univ y,hy⟩

/-- A single true chart through the given singleton closed source
produces global coverage. No line class or height comparison is needed. -/
theorem covers_of_retained (Q : Chart p) (z : Z) [Subsingleton ↥Z]
    (on : p z∈Q.V.1) (x : X) : ∃ P : Chart p, x∈P.V.1 := by
  classical
  by_cases e : x∈Set.range p
  · obtain ⟨w,rfl⟩ := e
    simpa only [Subsingleton.elim w z] using (show ∃ P : Chart p, p z∈P.V.1 from ⟨Q,on⟩)
  · exact empty_at p e

section RetainedFieldPoint

variable {E : Type u} [Field E] (r : Spec (CommRingCat.of E) ⟶ X) [IsClosedImmersion r]
variable (Q : Chart r)
variable (same_center : r (default : PrimeSpectrum E) ∈ Q.V.1)

/-- Consume the one exact chart at the named retained E-point: in the
modular application r is the rank-one graph of the chosen full read. -/
def centeredChart (x : X) : Chart r :=
  (covers_of_retained r Q (default : PrimeSpectrum E) same_center x).choose

theorem centeredChart_hits (x : X) : x∈(centeredChart r Q same_center x).V.1 :=
  (covers_of_retained r Q (default : PrimeSpectrum E) same_center x).choose_spec

def centeredFrame (x : X) {U : X.Opens}
    (h : U ≤ (centeredChart r Q same_center x).V.1) : Sec r U ≃ₗ[Γ(X,U)] Γ(X,U) :=
  frame (centeredChart r Q same_center x) h

/-- Same original positive section and same full ideal, chart by
chart, on the actual chosen base-changed curve. -/
theorem centered_cut (x : X) (V : X.affineOpens)
    (hV : V ≤ (centeredChart r Q same_center x).V) :
    Ideal.span {centeredFrame r Q same_center x hV (canon (p:=r) V.1)}=r.ker.ideal V :=
  canonical_affine (centeredChart r Q same_center x) V hV

end RetainedFieldPoint
end OriginalCyclicDivisorRetainedCartierCover318

#print axioms OriginalCyclicDivisorRetainedCartierCover318.empty_chart
#print axioms OriginalCyclicDivisorRetainedCartierCover318.centered_cut
