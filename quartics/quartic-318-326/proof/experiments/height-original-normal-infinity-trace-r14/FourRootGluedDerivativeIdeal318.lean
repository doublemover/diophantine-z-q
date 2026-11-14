module
public import FourRootDerivativeZeroIdeals318
public import AffineQuotientPullback318
public import GenericOpenPushout318
public section
noncomputable section
namespace FourRootGluedDerivativeIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootCoordinateOverlap318 FourRootDerivativeZeroIdeals318
variable (b:Fin 4→ℂ)
@[expose] def finiteArrow:CommRingCat.of (Affine b)⟶CommRingCat.of (InfinityOverlap b):=
  CommRingCat.ofHom (toInfinityBase b).toRingHom
@[expose] def infinityArrow:CommRingCat.of (Infinity b)⟶CommRingCat.of (InfinityOverlap b):=
  CommRingCat.ofHom (algebraMap (Infinity b) (InfinityOverlap b))
instance finiteArrow_open:IsOpenImmersion (Spec.map (finiteArrow b)):=by
  rw [finiteArrow,←FourRootGluedScheme318.intoFinite_eq]
  infer_instance
instance infinityArrow_open:IsOpenImmersion (Spec.map (infinityArrow b)):=
  FourRootGluedScheme318.intoInfinity_open b
abbrev finiteZero:Scheme:=Spec (CommRingCat.of (Affine b⧸finiteIdeal b))
abbrev infinityZero:Scheme:=Spec (CommRingCat.of (Infinity b⧸infinityIdeal b))
abbrev overlapZero:Scheme:=Spec (CommRingCat.of (InfinityOverlap b⧸overlapIdeal b))
@[expose] def toFinite:overlapZero b⟶finiteZero b:=
  Spec.map (AffineQuotientPullback318.arrow (finiteArrow b) (finiteIdeal b) (overlapIdeal b)
    (ideal_transition b).symm)
@[expose] def toInfinity:overlapZero b⟶infinityZero b:=
  Spec.map (AffineQuotientPullback318.arrow (infinityArrow b) (infinityIdeal b) (overlapIdeal b) rfl)
instance toFinite_open:IsOpenImmersion (toFinite b):=inferInstance
instance toInfinity_open:IsOpenImmersion (toInfinity b):=inferInstance
@[expose] def finiteInto:finiteZero b⟶FourRootGluedScheme318.scheme b:=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))≫FourRootGluedScheme318.finiteChart b
@[expose] def infinityInto:infinityZero b⟶FourRootGluedScheme318.scheme b:=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))≫FourRootGluedScheme318.infinityChart b
lemma compatible:toFinite b≫finiteInto b=toInfinity b≫infinityInto b:=by
  have hf:=(AffineQuotientPullback318.pullback_square (finiteArrow b)
    (finiteIdeal b) (overlapIdeal b) (ideal_transition b).symm).w
  have hi:=(AffineQuotientPullback318.pullback_square (infinityArrow b)
    (infinityIdeal b) (overlapIdeal b) rfl).w
  simp only [finiteInto,infinityInto,←Category.assoc]
  rw [←hf,←hi,Category.assoc,Category.assoc]
  change _≫(Spec.map (finiteArrow b)≫FourRootGluedScheme318.finiteChart b)=
    _≫(FourRootGluedScheme318.intoInfinity b≫FourRootGluedScheme318.infinityChart b)
  rw [finiteArrow,←FourRootGluedScheme318.intoFinite_eq,FourRootGluedScheme318.chart_overlap]
/-- A genuine glued closed-chart scheme, retaining the literal principal
quotient rings and their scheme-theoretic multiplicities. The derivative
identification is a subsequent local-frame theorem, not its definition. -/
abbrev zeroScheme:Scheme:=pushout (toFinite b) (toInfinity b)
@[expose] def finiteChart:finiteZero b⟶zeroScheme b:=pushout.inl _ _
@[expose] def infinityChart:infinityZero b⟶zeroScheme b:=pushout.inr _ _
instance finiteChart_open:IsOpenImmersion (finiteChart b):=by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (toFinite b) (toInfinity b)) WalkingSpan.left))
instance infinityChart_open:IsOpenImmersion (infinityChart b):=by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span (toFinite b) (toInfinity b)) WalkingSpan.right))
@[expose] def into:zeroScheme b⟶FourRootGluedScheme318.scheme b:=
  pushout.desc (finiteInto b) (infinityInto b) (compatible b)
@[simp,reassoc] lemma finiteChart_into:finiteChart b≫into b=finiteInto b:=pushout.inl_desc ..
@[simp,reassoc] lemma infinityChart_into:infinityChart b≫into b=infinityInto b:=pushout.inr_desc ..
lemma charts_cover(x:zeroScheme b):(∃p,finiteChart b p=x)∨(∃p,infinityChart b p=x):=by
  obtain ⟨i,q,hq⟩:=Scheme.IsLocallyDirected.ι_jointly_surjective (span (toFinite b) (toInfinity b)) x
  cases i with
  | none=>
    left
    refine ⟨toFinite b q,?_⟩
    change (toFinite b≫finiteChart b) q=x
    rw [show toFinite b≫finiteChart b=colimit.ι (span (toFinite b) (toInfinity b)) WalkingSpan.zero from
      colimit.w _ WalkingSpan.Hom.fst]
    exact hq
  | some j=>
    cases j with
    | left=>exact Or.inl ⟨q,hq⟩
    | right=>exact Or.inr ⟨q,hq⟩
end FourRootGluedDerivativeIdeal318
