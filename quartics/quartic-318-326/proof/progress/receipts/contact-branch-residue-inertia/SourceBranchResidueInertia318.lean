module
public import SourceBranchSignStabilizer318
public import SourceBranchPointAction318
public import Mathlib.RingTheory.Ideal.Pointwise
public section
noncomputable section
namespace SourceBranchResidueInertia318
open ContactKummerOrder318 Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) {F:Type*} [Field F] [Algebra ℚ F] [Algebra R F] [IsScalarTower ℚ R F]
variable (p:SourceOrder c→ₐ[R]F)
@[expose] def prime:Ideal (SourceOrder c):=RingHom.ker p.toRingHom
lemma prime_isPrime:(prime c p).IsPrime:=RingHom.ker_isPrime p.toRingHom
/-- Membership in Mathlib's actual ideal-theoretic inertia subgroup is
exactly triviality under the specified field-valued residue embedding. -/
theorem kernel_inertia_iff (s:SourceOrder c≃ₐ[R]SourceOrder c):
    s∈(prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)↔p.comp s.toAlgHom=p:=by
  rw [Ideal.mem_inertia]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    have hx:=h x
    change p (s x-x)=0 at hx
    change p (s x)=p x
    simpa only [map_sub,sub_eq_zero] using hx
  · intro h x
    have hx:=congrArg (fun f:SourceOrder c→ₐ[R]F=>f x) h
    change p (s x-x)=0
    change p (s x)=p x at hx
    rw [map_sub,hx,sub_self]
/-- The same action is literally trivial on the actual prime quotient,
not just on a list of coordinates. -/
theorem quotient_fixed (s:SourceOrder c≃ₐ[R]SourceOrder c)
    (h:s∈(prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)) (x:SourceOrder c):
    Ideal.Quotient.mk (prime c p) (s x)=Ideal.Quotient.mk (prime c p) x:=by
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.mem_inertia.mp h) x
variable (i:Fin 4) (ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i))
include ht
/-- Exact ideal-theoretic inertia criterion for each original root-sign
automorphism at the actual finite-contact source prime. -/
theorem sign_mem_iff (b:Fin 4→Bool):
    SourceSignFieldComparison318.sourceEquiv c b∈
      (prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)↔
      ∀j:Fin 4,j≠i→b j=false:=by
  rw [kernel_inertia_iff,SourceBranchSignStabilizer318.fixed_iff c p i ht]
theorem sign_mem_exactly (b:Fin 4→Bool):
    SourceSignFieldComparison318.sourceEquiv c b∈
      (prime c p).inertia (SourceOrder c≃ₐ[R]SourceOrder c)↔
      b=(fun _=>false)∨b=SourceCharacterFields318.flip i:=by
  rw [sign_mem_iff c p i ht,SourceBranchPointAction318.supported_iff]
theorem contact_flip_residue (x:SourceOrder c):
    Ideal.Quotient.mk (prime c p)
      (SourceSignFieldComparison318.sourceEquiv c (SourceCharacterFields318.flip i) x)=
        Ideal.Quotient.mk (prime c p) x:=
  quotient_fixed c p _ ((sign_mem_exactly c p i ht _).mpr (Or.inr rfl)) x
end SourceBranchResidueInertia318
