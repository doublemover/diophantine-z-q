module
public import ContactProjectiveClosedLocalRecovery318
public section
noncomputable section
namespace ContactProjectiveClosedRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318 ContactProjectiveClosedLocalRecovery318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  {Z : Scheme.{0}} (p : Z ⟶ ContactOriginalRelativePolynomialCharts318.curve R c) [IsClosedImmersion p]
local notation "D" => ContactProjectiveClosedData318.datum R c p
local notation "Q" => family R c D
local notation "q" => into R c D
local notation "U" => SchemeOpenPushout318.cover
  (ContactProjectiveQuotientOverlap318.finiteMap R c D)
  (ContactProjectiveQuotientOverlap318.infinityMap R c D)
@[expose] def localForward (b : Bool) : U.X b ⟶ Z := by
  cases b
  · exact finiteToOriginal R c p
  · exact infinityToOriginal R c p
lemma localForward_factor (b : Bool) : localForward R c p b ≫ p=U.f b ≫ q := by
  cases b
  · exact (finiteToOriginal_into R c p).trans (finite_square R c D).w.symm
  · exact (infinityToOriginal_into R c p).trans (infinity_square R c D).w.symm
@[expose] def forward : Q ⟶ Z :=
  SchemeMonoLocalLift318.lift U p q (localForward R c p) (localForward_factor R c p)
@[reassoc] lemma forward_into : forward R c p ≫ p=q :=
  SchemeMonoLocalLift318.lift_factor U p q (localForward R c p) (localForward_factor R c p)
local notation "V" => (ContactGlobalZeroClosed318.originalCover R c).pullback₁ p
@[expose] def localBackward (i : Fin 2) : V.X i ⟶ Q := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact (finiteComparison R c p).hom ≫ finiteChart R c D
  · exact (infinityComparison R c p).hom ≫ infinityChart R c D
lemma localBackward_factor (i : Fin 2) : localBackward R c p i ≫ q=V.f i ≫ p := by
  fin_cases i
  · change ((finiteComparison R c p).hom ≫ finiteChart R c D) ≫ q=_
    rw [Category.assoc,(finite_square R c D).w,← Category.assoc,finite_comparison_into]
    exact pullback.condition.symm
  · change ((infinityComparison R c p).hom ≫ infinityChart R c D) ≫ q=_
    rw [Category.assoc,(infinity_square R c D).w,← Category.assoc,infinity_comparison_into]
    exact pullback.condition.symm
@[expose] def backward : Z ⟶ Q :=
  SchemeMonoLocalLift318.lift V q p (localBackward R c p) (localBackward_factor R c p)
@[reassoc] lemma backward_into : backward R c p ≫ q=p :=
  SchemeMonoLocalLift318.lift_factor V q p (localBackward R c p) (localBackward_factor R c p)
/-- The quotient reconstructed from the full affine restriction ideals
is the actual original closed scheme, over the original projective source. -/
@[expose] def comparison : Q ≅ Z where
  hom := forward R c p
  inv := backward R c p
  hom_inv_id := by
    apply (cancel_mono q).mp
    rw [Category.assoc,backward_into,forward_into,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono p).mp
    rw [Category.assoc,forward_into,backward_into,Category.id_comp]
lemma idealSheaf_eq : ContactProjectiveQuotientIdealSheaf318.idealSheaf R c D=p.ker := by
  have h := Scheme.Hom.ker_comp_of_isIso (comparison R c p).hom p
  change (forward R c p ≫ p).ker=_ at h
  rw [forward_into] at h
  exact h
end ContactProjectiveClosedRecovery318
