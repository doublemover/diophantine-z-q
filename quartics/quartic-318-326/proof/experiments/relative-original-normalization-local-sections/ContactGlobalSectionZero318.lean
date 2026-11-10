module
public import ContactOriginalSectionZeros318
public import AffineQuotientPullback318
public import GenericOpenPushout318
public section
noncomputable section
namespace ContactGlobalSectionZero318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalRelativeOverlap318 ContactOriginalSectionZeros318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

@[expose] def toFinite : overlapZero R c L s ⟶ finiteZero R c L s :=
  Spec.map (AffineQuotientPullback318.arrow (finiteArrow R c)
    (finiteIdeal R c L s) (overlapIdeal R c L s) (finite_overlap R c L s))
@[expose] def toInfinity : overlapZero R c L s ⟶ infinityZero R c L s :=
  Spec.map (AffineQuotientPullback318.arrow (infinityArrow R c)
    (infinityIdeal R c L s) (overlapIdeal R c L s) (infinity_overlap R c L s))
instance : IsOpenImmersion (toFinite R c L s) := inferInstance
instance : IsOpenImmersion (toInfinity R c L s) := inferInstance

@[expose] def finiteIntoOriginal : finiteZero R c L s ⟶ curve R c :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s))) ≫ finiteInto R c
@[expose] def infinityIntoOriginal : infinityZero R c L s ⟶ curve R c :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s))) ≫ infinityInto R c

lemma compatible : toFinite R c L s ≫ finiteIntoOriginal R c L s =
    toInfinity R c L s ≫ infinityIntoOriginal R c L s := by
  have hf := (AffineQuotientPullback318.pullback_square (finiteArrow R c)
    (finiteIdeal R c L s) (overlapIdeal R c L s) (finite_overlap R c L s)).w
  have hi := (AffineQuotientPullback318.pullback_square (infinityArrow R c)
    (infinityIdeal R c L s) (overlapIdeal R c L s) (infinity_overlap R c L s)).w
  simp only [finiteIntoOriginal,infinityIntoOriginal,← Category.assoc]
  rw [← hf,← hi,Category.assoc,Category.assoc]
  change _ ≫ (finiteEdge R c ≫ finiteInto R c) = _ ≫ (infinityEdge R c ≫ infinityInto R c)
  rw [finiteEdge_into,infinityEdge_into]

/-- The actual global scheme obtained by gluing the original section's
whole finite/infinity zero quotients along their full original zero overlap.
Its construction uses Cartesian quotient squares, not equality of zero sets. -/
abbrev scheme : Scheme := pushout (toFinite R c L s) (toInfinity R c L s)
@[expose] def finiteChart : finiteZero R c L s ⟶ scheme R c L s := pushout.inl _ _
@[expose] def infinityChart : infinityZero R c L s ⟶ scheme R c L s := pushout.inr _ _
instance : IsOpenImmersion (finiteChart R c L s) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι
    (span (toFinite R c L s) (toInfinity R c L s)) WalkingSpan.left))
instance : IsOpenImmersion (infinityChart R c L s) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι
    (span (toFinite R c L s) (toInfinity R c L s)) WalkingSpan.right))

@[expose] def into : scheme R c L s ⟶ curve R c :=
  pushout.desc (finiteIntoOriginal R c L s) (infinityIntoOriginal R c L s) (compatible R c L s)
@[simp,reassoc] lemma finiteChart_into : finiteChart R c L s ≫ into R c L s =
    finiteIntoOriginal R c L s := pushout.inl_desc ..
@[simp,reassoc] lemma infinityChart_into : infinityChart R c L s ≫ into R c L s =
    infinityIntoOriginal R c L s := pushout.inr_desc ..

lemma intersection_square : IsPullback (toFinite R c L s) (toInfinity R c L s)
    (finiteChart R c L s) (infinityChart R c L s) := GenericOpenPushout318.square _ _

lemma charts_cover (x : scheme R c L s) :
    (∃ a,finiteChart R c L s a=x) ∨ (∃ b,infinityChart R c L s b=x) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (toFinite R c L s) (toInfinity R c L s)) x
  cases i with
  | none =>
    left
    refine ⟨toFinite R c L s q,?_⟩
    change (toFinite R c L s ≫ finiteChart R c L s) q=x
    rw [show toFinite R c L s ≫ finiteChart R c L s =
      colimit.ι (span (toFinite R c L s) (toInfinity R c L s)) WalkingSpan.zero from
      colimit.w _ WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩
end ContactGlobalSectionZero318
