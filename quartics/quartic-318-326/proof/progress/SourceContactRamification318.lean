module
public import SourceContactPrime318
public section
noncomputable section
namespace SourceContactRamification318
open ContactKummerOrder318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance sourceDomain:IsDomain (SourceOrder c):=source_domain c
local instance sourceFinite:Module.Finite R (SourceOrder c):=(source_finite_free c).1
local instance sourceFlat:Module.Flat R (SourceOrder c):=(SourceOrderGaloisAction318.finite_flat c).2
local instance groupFinite:Finite (SourceOrderGaloisAction318.G c):=SourceOrderGaloisAction318.group_finite c
local instance groupGalois:IsGaloisGroup (SourceOrderGaloisAction318.G c) R (SourceOrder c):=
  SourceOrderGaloisAction318.galoisGroup c
variable (Q:Ideal (SourceOrder c)) [Q.IsPrime] (i:Fin 4)
    (hc:algebraMap R (SourceOrder c)
      (Polynomial.X-Polynomial.C (LinearContactSquareclass318.contacts i))∈Q)
local instance contactPrime:(SourceContactPrime318.prime i).IsPrime:=
  (SourceContactPrime318.maximal i).isPrime
local instance separableResidue:
    Algebra.HasSeparableResidueFieldsAt R (SourceOrder c) (SourceContactPrime318.prime i):=
  SourceContactPrime318.residue_separable c i
include hc
/-- The complete source-order ideal inertia at every actual contact prime
has order two, using its canonical residue point. -/
theorem ideal_inertia_card:Nat.card (Q.inertia (SourceOrderGaloisAction318.G c))=2:=by
  letI:=SourcePrimeValuationInertia318.residueBase c Q
  letI:=SourcePrimeValuationInertia318.residueRat c Q
  letI:=SourcePrimeValuationInertia318.baseTower c Q
  letI:=SourcePrimeValuationInertia318.ratTower c Q
  have h:=SourceBranchFullInertia318.inertia_card c
    (SourcePrimeValuationInertia318.residuePoint c Q) i
    (SourcePrimeValuationInertia318.residue_contact c Q i hc)
  rw [SourcePrimeValuationInertia318.kernel_exact] at h
  exact h

/-- The ramification index of the exact finite contact in the entire
original polynomial order is two. The cardinality-to-index theorem is
applied with actual Galois action, finite flatness and separable residue fields. -/
theorem ramificationIdxIn_two:
    Ideal.ramificationIdxIn (SourceContactPrime318.prime i) (SourceOrder c)=2:=by
  letI:Q.LiesOver (SourceContactPrime318.prime i):=SourceContactPrime318.liesOver i c Q hc
  have h:=Ideal.card_inertia_eq_ramificationIdxIn
    (G:=SourceOrderGaloisAction318.G c) (SourceContactPrime318.prime i) Q
  exact h.symm.trans (ideal_inertia_card c Q i hc)

/-- At every actual prime above any of the four finite contacts, the
literal ideal ramification index relative to the original Q[t] base is two. -/
theorem ramificationIdx_two:Q.ramificationIdx R=2:=by
  letI:Q.LiesOver (SourceContactPrime318.prime i):=SourceContactPrime318.liesOver i c Q hc
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx (SourceContactPrime318.prime i) Q
    (SourceOrderGaloisAction318.G c)]
  exact ramificationIdxIn_two c Q i hc
end SourceContactRamification318
