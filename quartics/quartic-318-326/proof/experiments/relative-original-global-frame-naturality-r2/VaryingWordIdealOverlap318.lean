module
public import VaryingNormalizedUniversalFamily318
public section
noncomputable section
namespace VaryingWordIdealOverlap318
open VaryingNormalizedWordOverlap318 VaryingNormalizedOverlapFrames318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
local notation "B" => (S ⊗[R] A)
variable (d : Point R A ι w S v)
local notation "F" t p => VaryingNormalizedWordFrame318.framed R A ι t S p

/-- Both normalized chart presentations define the SAME whole ideal in
the literal base-changed original source, including nilpotents. -/
lemma transition_ideal :
    ideal (F v (transition R A ι w S v d).val).action
      (F v (transition R A ι w S v d).val).marked=
    ideal (F w d.val).action (F w d.val).marked := by
  have h := VaryingWordTriplePoints318.frame_transition R A ι w v S d
  change F v (transition R A ι w S v d).val=
    CyclicWordNormalization318.normalize S B ι (F w d.val)
      (fun j => (1 : S) ⊗ₜ[R] (v j).prod) (toFrames R A ι w S v d).property at h
  rw [h]
  exact congrArg Subtype.val
    (CyclicWordNormalization318.normalize_ideal S B ι (F w d.val) _ _)

/-- The overlap family comparison is the quotient algebra equivalence
induced by equality of the actual ideals, with source elements unchanged. -/
@[expose] def quotientEquiv :
    (B ⧸ ideal (F v (transition R A ι w S v d).val).action
      (F v (transition R A ι w S v d).val).marked) ≃ₐ[S]
    (B ⧸ ideal (F w d.val).action (F w d.val).marked) :=
  Ideal.quotientEquivAlgOfEq S (transition_ideal R A ι w v S d)
lemma quotientEquiv_mk (a : B) : quotientEquiv R A ι w v S d
    (Ideal.Quotient.mk _ a)=Ideal.Quotient.mk _ a :=
  Ideal.quotientEquivAlgOfEq_mk S (transition_ideal R A ι w v S d) a
end VaryingWordIdealOverlap318
