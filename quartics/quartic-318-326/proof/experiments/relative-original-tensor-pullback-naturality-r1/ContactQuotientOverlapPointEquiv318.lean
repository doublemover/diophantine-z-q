module
public import ContactQuotientOverlapOpen318
public section
noncomputable section
namespace ContactQuotientOverlapPointEquiv318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
local notation "E" => VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S
local notation "π" => VaryingWordGlobalFamilyProjection318.projection ℚ (ring c a) (Fin n)
local notation "q" => VaryingWordGlobalOriginalMap318.original ℚ (ring c a) (Fin n)
@[expose] def recover (x : Point c a b n S) : ContactQuotientOverlapEquiv318.Overlap c a b S n := by
  refine ⟨E.symm (underlying c a b n S x),?_⟩
  apply (supported_iff_universal c a b n S _).mpr
  rw [E.apply_symm_apply]
  exact FiniteFamilyAvoidanceFactor318.supported_comp π q (sourceOpen c a b) x.val
lemma recover_classify (I : ContactQuotientOverlapEquiv318.Overlap c a b S n) :
    recover c a b n S (classify c a b n S I)=I := by
  apply Subtype.ext
  change E.symm (underlying c a b n S (classify c a b n S I))=I.val
  rw [classify_underlying,E.symm_apply_apply]
lemma classify_recover (x : Point c a b n S) : classify c a b n S (recover c a b n S x)=x := by
  apply Subtype.ext
  apply (cancel_mono (parameterOpen c a b n).ι).mp
  exact congrArg Subtype.val ((classify_underlying c a b n S (recover c a b n S x)).trans
    (E.apply_symm_apply (underlying c a b n S x)))
/-- Actual avoidance open points represent the intrinsic supported
full-quotient functor on ALL affine coefficient tests. -/
@[expose] def equivalence : ContactQuotientOverlapEquiv318.Overlap c a b S n ≃ Point c a b n S where
  toFun := classify c a b n S
  invFun := recover c a b n S
  left_inv := recover_classify c a b n S
  right_inv := classify_recover c a b n S
/-- Genuine point equivalence of the two ACTUAL avoidance open schemes.
Realizing it as a scheme isomorphism remains a separate construction. -/
@[expose] def transition : Point c a b n S ≃ Point c b a n S :=
  (equivalence c a b n S).symm.trans
    ((ContactQuotientOverlapEquiv318.equivalence c a b S n).trans (equivalence c b a n S))
end ContactQuotientOverlapPointEquiv318
