module
public import ContactSectionQuotientData318
public import SchemeMonoLocalLift318
public section
noncomputable section
namespace ContactSectionQuotientComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
local notation "D" => ContactSectionQuotientData318.datum R c L s
local notation "Q" => ContactProjectiveQuotientGluing318.family R c D
local notation "Z" => ContactGlobalSectionZero318.scheme R c L s
local notation "q" => ContactProjectiveQuotientGluing318.into R c D
local notation "z" => ContactGlobalSectionZero318.into R c L s
local notation "U" => SchemeOpenPushout318.cover
  (ContactProjectiveQuotientOverlap318.finiteMap R c D)
  (ContactProjectiveQuotientOverlap318.infinityMap R c D)
@[expose] def localForward (b : Bool) : U.X b ⟶ Z := by
  cases b
  · exact ContactGlobalSectionZero318.finiteChart R c L s
  · exact ContactGlobalSectionZero318.infinityChart R c L s
lemma localForward_factor (b : Bool) : localForward R c L s b ≫ z=U.f b ≫ q := by
  cases b
  · exact (ContactGlobalSectionZero318.finiteChart_into R c L s).trans
      (ContactProjectiveQuotientGluing318.finite_square R c D).w.symm
  · exact (ContactGlobalSectionZero318.infinityChart_into R c L s).trans
      (ContactProjectiveQuotientGluing318.infinity_square R c D).w.symm
@[expose] def forward : Q ⟶ Z :=
  SchemeMonoLocalLift318.lift U z q (localForward R c L s) (localForward_factor R c L s)
@[reassoc] lemma forward_into : forward R c L s ≫ z=q :=
  SchemeMonoLocalLift318.lift_factor U z q (localForward R c L s) (localForward_factor R c L s)
local notation "V" => ContactGlobalResidueFlat318.cover R c L s
@[expose] def localBackward (i : Fin 2) : V.X i ⟶ Q := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact ContactProjectiveQuotientGluing318.finiteChart R c D
  · exact ContactProjectiveQuotientGluing318.infinityChart R c D
lemma localBackward_factor (i : Fin 2) : localBackward R c L s i ≫ q=V.f i ≫ z := by
  fin_cases i
  · exact (ContactProjectiveQuotientGluing318.finite_square R c D).w.trans
      (ContactGlobalSectionZero318.finiteChart_into R c L s).symm
  · exact (ContactProjectiveQuotientGluing318.infinity_square R c D).w.trans
      (ContactGlobalSectionZero318.infinityChart_into R c L s).symm
@[expose] def backward : Z ⟶ Q :=
  SchemeMonoLocalLift318.lift V q z (localBackward R c L s) (localBackward_factor R c L s)
@[reassoc] lemma backward_into : backward R c L s ≫ q=z :=
  SchemeMonoLocalLift318.lift_factor V q z (localBackward R c L s) (localBackward_factor R c L s)
/-- The arbitrary-ideal gluing is the SAME original section-zero model,
with the exact original source embedding, not just an isomorphic fiber set. -/
@[expose] def comparison : Q ≅ Z where
  hom := forward R c L s
  inv := backward R c L s
  hom_inv_id := by
    apply (cancel_mono q).mp
    rw [Category.assoc,backward_into,forward_into,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono z).mp
    rw [Category.assoc,forward_into,backward_into,Category.id_comp]
end ContactSectionQuotientComparison318
