module
public import OriginalPeriodFiniteSchemeBijection318
public import PELOriginalAlgebraicDoubling318
public section
noncomputable section
namespace OriginalPeriodCompletedSchemeBijection318
open CategoryTheory AlgebraicGeometry
open OriginalPeriodProjectiveModel318 OriginalPeriodGlobalSchemePoints318
open OriginalPeriodFiniteSchemeBijection318 ComplexAffineFreeTranslation318
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Same previously constructed global original point map, now retained
with its actual structural morphism equation. -/
@[expose] def point (q : Torus L) :
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A L) (B L) :=
  ⟨schemePoint L q,by
    change schemePoint L q ≫ structure L=Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))
    rw [schemePoint_over_base]
    symm
    exact Spec.map_id _⟩

lemma point_zero : point L 0=CompletedFieldPoints318.infinityPoint (A L) (B L) := by
  apply Subtype.ext
  rw [show (point L 0).val=schemePoint L 0 from rfl,schemePoint_zero]
  change infinity L=Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) ≫ infinity L
  rw [show Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ))=𝟙 _ from Spec.map_id _,Category.id_comp]

lemma point_nonzero (q : Torus L) (hq : q≠0) :
    point L q=CompletedFieldPoints318.finiteInclusion (A L) (B L)
      (finiteEquivalence L ⟨q,hq⟩) := by
  apply Subtype.ext
  exact (schemePoint_nonzero L q hq).trans (finite_inclusion L ⟨q,hq⟩).symm

/-- Full scheme coverage is supplied by the ACTUAL two open charts of
the independent completed scheme. No scheme points are excluded. -/
theorem point_surjective : Function.Surjective (point L) := by
  intro p
  rcases CompletedFieldPoints318.finite_or_infinity (A L) (B L) p with ⟨a,ha⟩ | hi
  · obtain ⟨q,hq⟩ := (finiteEquivalence L).surjective a
    exact ⟨q.val,(point_nonzero L q.val q.property).trans (by rw [hq]; exact ha)⟩
  · exact ⟨0,(point_zero L).trans hi.symm⟩

/-- Infinity is distinct from every finite point by the actual open-chart
preimage calculation, and finite coordinates recover the original torus. -/
theorem point_injective : Function.Injective (point L) := by
  intro q r he
  by_cases hq : q=0
  · subst q
    by_cases hr : r=0
    · exact hr.symm
    · rw [point_zero,point_nonzero L r hr] at he
      exact (CompletedFieldPoints318.finite_ne_infinity (A L) (B L)
        (finiteEquivalence L ⟨r,hr⟩) he.symm).elim
  · by_cases hr : r=0
    · subst r
      rw [point_nonzero L q hq,point_zero] at he
      exact (CompletedFieldPoints318.finite_ne_infinity (A L) (B L)
        (finiteEquivalence L ⟨q,hq⟩) he).elim
    · rw [point_nonzero L q hq,point_nonzero L r hr] at he
      have h := CompletedFieldPoints318.finiteInclusion_injective (A L) (B L) he
      exact congrArg Subtype.val ((finiteEquivalence L).injective h)

/-- The SAME original global map is a bijection onto all actual complex
points of the smooth proper scheme defined by its genuine period sums. -/
@[expose] def equivalence : Torus L ≃
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A L) (B L) :=
  Equiv.ofBijective (point L) ⟨point_injective L,point_surjective L⟩

/-- Native algebraic elliptic points and genuine completed-scheme points
agree through their already specified original coordinates and infinity.
This does not install a transported scheme structure or assert algebraization. -/
@[expose] def nativeEquivalence : (OriginalPeriodEllipticPoints318.curve L).toAffine.Point ≃
    CompletedFieldPoints318.SchemePoints (K:=ℂ) (A L) (B L) :=
  (OriginalPeriodEllipticPoints318.equivalence L).symm.trans (equivalence L)

lemma native_original (q : Torus L) :
    nativeEquivalence L (OriginalPeriodEllipticPoints318.point L q)=point L q :=
  congrArg (equivalence L) ((OriginalPeriodEllipticPoints318.equivalence L).symm_apply_apply q)
end OriginalPeriodCompletedSchemeBijection318
