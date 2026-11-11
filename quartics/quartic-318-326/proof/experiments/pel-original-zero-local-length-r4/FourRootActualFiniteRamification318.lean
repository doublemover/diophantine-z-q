module
public import FourRootActualOrderGalois318
public import Mathlib.RingTheory.Polynomial.Ideal
public section
noncomputable section
namespace FourRootActualFiniteRamification318
open Polynomial FourRootActualGenericField318 FourRootAffineTensorPresentation318
open FourRootActualFractionField318 FourRootActualResidueInertia318 FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance affineFinite:Module.Finite P (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFlat:Module.Flat P (A b):=(FourRootActualOrderGalois318.finite_flat b).2
local instance groupFinite:Finite (FourRootActualOrderGalois318.G b):=
  FourRootActualOrderGalois318.group_finite b hb
local instance groupGalois:IsGaloisGroup (FourRootActualOrderGalois318.G b) P (A b):=
  FourRootActualOrderGalois318.galoisGroup b hb

@[expose] def contactPrime (j:Fin 4):Ideal P:=Ideal.span {X-C (b j)}
lemma contact_maximal (j:Fin 4):(contactPrime b j).IsMaximal:=by
  rw [contactPrime,←Polynomial.ker_evalRingHom]
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨C c,Polynomial.eval_C⟩

lemma contact_membership (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    algebraMap P (A b) (X-C (b j))∈finitePrime b p:=by
  have he:finiteEvaluation b p (FourRootAffineCoordinateRing318.coordinate b none)=p.val.1:=by
    have h:=(FourRootAffineCoordinateRing318.pointEquiv b).apply_symm_apply p
    exact congrArg (fun q:FinitePoints b=>q.val.1) h
  change finiteEvaluation b p (Polynomial.aeval
    (FourRootAffineCoordinateRing318.coordinate b none) (X-C (b j)))=0
  simp only [map_sub,Polynomial.aeval_X,Polynomial.aeval_C,AlgHom.commutes,he,hp,
    Algebra.algebraMap_self,sub_self]

lemma liesOver (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    (finitePrime b p).LiesOver (contactPrime b j):=by
  letI: (finitePrime b p).IsPrime:=finite_prime b p
  constructor
  apply (contact_maximal b j).eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance:((finitePrime b p).under P).IsPrime))
  exact Ideal.span_le.mpr (by
    intro r hr
    rcases Set.mem_singleton_iff.mp hr with rfl
    exact contact_membership b j p hp)

lemma separableResidue (j:Fin 4):
    Algebra.HasSeparableResidueFieldsAt P (A b) (contactPrime b j):=by
  letI:(contactPrime b j).IsPrime:=(contact_maximal b j).isPrime
  letI:Algebra.IsIntegral P (A b):=Algebra.IsIntegral.of_finite P (A b)
  letI:Algebra ℂ (contactPrime b j).ResidueField:=
    ((algebraMap P (contactPrime b j).ResidueField).comp (algebraMap ℂ P)).toAlgebra
  letI:CharZero (contactPrime b j).ResidueField:=
    Algebra.charZero_of_charZero ℂ (contactPrime b j).ResidueField
  infer_instance

/-- Actual algebraic ramification index of the SAME whole finite chart
at every original complex branch point. The cardinality-to-index theorem
uses constructed full Galois action, finite flatness and separable residue
fields, not an analytic local-degree assertion or a known-label count. -/
theorem ramificationIdxIn_two (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    Ideal.ramificationIdxIn (contactPrime b j) (A b)=2:=by
  letI:(contactPrime b j).IsPrime:=(contact_maximal b j).isPrime
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  letI:(finitePrime b p).LiesOver (contactPrime b j):=liesOver b j p hp
  letI:Algebra.HasSeparableResidueFieldsAt P (A b) (contactPrime b j):=separableResidue b j
  have h:=Ideal.card_inertia_eq_ramificationIdxIn
    (G:=FourRootActualOrderGalois318.G b) (contactPrime b j) (finitePrime b p)
  exact h.symm.trans (FourRootFullFiniteInertia318.full_inertia_card b hb j p hp)

theorem ramificationIdx_two (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    (finitePrime b p).ramificationIdx P=2:=by
  letI:(contactPrime b j).IsPrime:=(contact_maximal b j).isPrime
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  letI:(finitePrime b p).LiesOver (contactPrime b j):=liesOver b j p hp
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx (contactPrime b j) (finitePrime b p)
    (FourRootActualOrderGalois318.G b)]
  exact ramificationIdxIn_two b hb j p hp
end FourRootActualFiniteRamification318
