module
public import SourceOrderAutomorphisms318
public import SourceBranchResidueInertia318
public import FourRootOrderSignAction318
public section
noncomputable section
namespace SourceBranchFullInertia318
open ContactKummerOrder318 Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
lemma identity_sign:SourceSignFieldComparison318.sourceEquiv c (fun _=>false)=1:=
  FourRootOrderSignAction318.identity (coefficient c)
variable {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F) (i:Fin 4)
    (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
include ht
/-- The full actual Q[t]-algebra automorphism group's ideal inertia is
exactly identity and the single root flip at the finite contact. -/
theorem mem_exactly (e:SourceOrder c≃ₐ[R]SourceOrder c):
    e∈(SourceBranchResidueInertia318.prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)↔
      e=1∨e=SourceSignFieldComparison318.sourceEquiv c (SourceCharacterFields318.flip i):=by
  obtain ⟨b,rfl⟩:=SourceOrderAutomorphisms318.sign_surjective c e
  rw [SourceBranchResidueInertia318.sign_mem_exactly c p i ht,←identity_sign c]
  simp only [(SourceOrderAutomorphisms318.sign_injective c).eq_iff]
/-- The equivalence preserves the actual inertia elements via their
unique source-sign patterns; its one free bit is the contact root. -/
@[expose] def inertiaEquiv:
    (SourceBranchResidueInertia318.prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)≃Bool:=
  ((SourceOrderAutomorphisms318.signEquiv c).subtypeEquiv
    (fun b=>(SourceBranchResidueInertia318.sign_mem_iff c p i ht b).symm)).symm.trans
      (SourceBranchPointAction318.supportedEquiv i)
theorem inertia_card:Nat.card
    ((SourceBranchResidueInertia318.prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c))=2:=by
  rw [Nat.card_congr (inertiaEquiv c p i ht)]
  simp
end SourceBranchFullInertia318
