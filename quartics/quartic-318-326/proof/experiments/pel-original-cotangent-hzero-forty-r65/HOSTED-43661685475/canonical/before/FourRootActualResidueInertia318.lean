module
public import FourRootActionStabilizers318
public import Mathlib.RingTheory.Ideal.Pointwise
public section
noncomputable section
namespace FourRootActualResidueInertia318
open FourRootNormalizedPointCharts318 FourBinaryCharacters318
variable (b:Fin 4→ℂ)

/-- Actual ideal inertia at the kernel of a specified complex-valued
point is exactly equality of its residue evaluation maps. -/
lemma kernel_inertia_iff {A:Type*} [CommRing A] [Algebra ℂ A]
    (p:A→ₐ[ℂ]ℂ) (e:A≃ₐ[ℂ]A):
    e∈(RingHom.ker p.toRingHom).inertia (A≃ₐ[ℂ]A) ↔ p.comp e.toAlgHom=p:=by
  rw [Ideal.mem_inertia]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    have hx:=h x
    change p (e x-x)=0 at hx
    change p (e x)=p x
    simpa only [map_sub,sub_eq_zero] using hx
  · intro h x
    have hx:=AlgHom.congr_fun h x
    change p (e x-x)=0
    change p (e x)=p x at hx
    rw [map_sub,hx,sub_self]

@[expose] def finiteEvaluation (p:FinitePoints b):FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]ℂ:=
  (FourRootAffineCoordinateRing318.pointEquiv b).symm p
@[expose] def finitePrime (p:FinitePoints b):Ideal (FourRootAffineCoordinateRing318.Ring b):=
  RingHom.ker (finiteEvaluation b p).toRingHom
lemma finite_prime (p:FinitePoints b):(finitePrime b p).IsPrime:=
  RingHom.ker_isPrime (finiteEvaluation b p).toRingHom

lemma finite_sign_inertia (g:FourBinaryCharacters318.Group) (p:FinitePoints b):
    FourRootCoordinateRingSigns318.finiteEquiv b g∈
      (finitePrime b p).inertia (FourRootAffineCoordinateRing318.Ring b≃ₐ[ℂ]FourRootAffineCoordinateRing318.Ring b) ↔
      ∀i,p.val.2 i≠0→coordinate (F:=ℂ) i g=1:=by
  rw [kernel_inertia_iff]
  rw [←(FourRootAffineCoordinateRing318.pointEquiv b).injective.eq_iff]
  change FourRootAffineCoordinateRing318.point b
    ((finiteEvaluation b p).comp (FourRootCoordinateRingSigns318.finiteEnd b g))=
      FourRootAffineCoordinateRing318.point b (finiteEvaluation b p) ↔ _
  rw [FourRootCoordinateRingSigns318.finite_point]
  have hp:FourRootAffineCoordinateRing318.point b (finiteEvaluation b p)=p:=
    (FourRootAffineCoordinateRing318.pointEquiv b).apply_symm_apply p
  rw [hp]
  exact FourRootActionStabilizers318.finite_fixed_iff b g p

/-- At each actual finite branch point, ideal inertia on the original
sixteen deck automorphisms is exactly the one free branch-root sign. -/
theorem finite_branch_inertia (hb:Function.Injective b)
    (g:FourBinaryCharacters318.Group) (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    FourRootCoordinateRingSigns318.finiteEquiv b g∈
      (finitePrime b p).inertia (FourRootAffineCoordinateRing318.Ring b≃ₐ[ℂ]FourRootAffineCoordinateRing318.Ring b) ↔
      ∀i,i≠j→coordinate (F:=ℂ) i g=1:=by
  rw [finite_sign_inertia,←FourRootActionStabilizers318.finite_fixed_iff]
  exact FourRootActionStabilizers318.finite_branch_fixed_iff b hb g j p hp

@[expose] def infinityEvaluation (p:InfinityPoints b):FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]ℂ:=
  (FourRootInfinityCoordinateRing318.pointEquiv b).symm p
@[expose] def infinityPrime (p:InfinityPoints b):Ideal (FourRootInfinityCoordinateRing318.Ring b):=
  RingHom.ker (infinityEvaluation b p).toRingHom
lemma infinity_prime (p:InfinityPoints b):(infinityPrime b p).IsPrime:=
  RingHom.ker_isPrime (infinityEvaluation b p).toRingHom

lemma infinity_sign_fixed (g:FourBinaryCharacters318.Group) (p:InfinityPoints b) (hp:p.val.1=0):
    FourRootNormalizedSignAction318.infinity b g p=p ↔
      ∀i,coordinate (F:=ℂ) i g=coordinate (F:=ℂ) 0 g:=by
  let s:InfinitySigns:=⟨p.val.2,p.property.1,by
    intro i
    simpa only [hp,zero_pow (by decide:2≠0),mul_zero,add_zero] using p.property.2 i⟩
  rw [←FourRootActionStabilizers318.infinity_fixed_iff g s]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun q:InfinityPoints b=>q.val.2) h
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · change coordinate (F:=ℂ) 0 g*p.val.1=p.val.1
      rw [hp,mul_zero]
    · exact congrArg Subtype.val h

/-- Every one of the eight normalized infinity points has actual ideal
inertia on the original deck group precisely the simultaneous sign flip. -/
theorem infinity_inertia (g:FourBinaryCharacters318.Group) (p:InfinityPoints b) (hp:p.val.1=0):
    FourRootCoordinateRingSigns318.infinityEquiv b g∈
      (infinityPrime b p).inertia (FourRootInfinityCoordinateRing318.Ring b≃ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b) ↔
      ∀i,coordinate (F:=ℂ) i g=coordinate (F:=ℂ) 0 g:=by
  rw [kernel_inertia_iff]
  have he:((infinityEvaluation b p).comp (FourRootCoordinateRingSigns318.infinityEquiv b g).toAlgHom=
      infinityEvaluation b p) ↔
      FourRootNormalizedSignAction318.infinity b g p=p:=by
    rw [←(FourRootInfinityCoordinateRing318.pointEquiv b).injective.eq_iff]
    change FourRootInfinityCoordinateRing318.point b
      ((infinityEvaluation b p).comp (FourRootCoordinateRingSigns318.infinityEnd b g))=
      FourRootInfinityCoordinateRing318.point b (infinityEvaluation b p) ↔ _
    rw [FourRootCoordinateRingSigns318.infinity_point]
    have hq:FourRootInfinityCoordinateRing318.point b (infinityEvaluation b p)=p:=
      (FourRootInfinityCoordinateRing318.pointEquiv b).apply_symm_apply p
    rw [hq]
  rw [he]
  exact infinity_sign_fixed b g p hp
end FourRootActualResidueInertia318
