module
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section
namespace PrimeLocalizationInertia318
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A:Type*} [CommRing A] (P:Ideal A) [P.IsPrime]
variable (S:Type*) [CommRing S] [Algebra A S] [IsLocalization P.primeCompl S]
variable (e:A≃+*A) (he:P=P.comap e)
include he
lemma primeCompl_map:P.primeCompl.map e.toMonoidHom=P.primeCompl:=by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change e x∉P
    have h: x∈P↔e x∈P:=by
      conv_lhs=>rw [he]
      rfl
    exact fun hx'=>hx (h.mpr hx')
  · intro hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    change e.symm y∉P
    have h:e.symm y∈P↔y∈P:=by
      conv_lhs=>rw [he]
      simp only [Ideal.mem_comap,e.apply_symm_apply]
    exact fun hx=>hy (h.mp hx)

/-- The actual extension of the specified prime-preserving automorphism
to any chosen localization at that same prime. -/
@[expose] def lift:S≃+*S:=
  IsLocalization.ringEquivOfRingEquiv S S e (primeCompl_map P e he)
lemma lift_algebraMap (x:A):lift P S e he (algebraMap A S x)=algebraMap A S (e x):=
  IsLocalization.ringEquivOfRingEquiv_eq (primeCompl_map P e he) x

variable [IsLocalRing S]
/-- Triviality on the full local residue field is equivalent to triviality
modulo the original prime. The localization is not replaced by its generic field. -/
theorem residue_trivial_iff:
    (∀x:S,IsLocalRing.residue S (lift P S e he x)=IsLocalRing.residue S x) ↔
      ∀x:A,e x-x∈P:=by
  constructor
  · intro h x
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S P (e x-x)).mp
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub,map_sub]
    exact sub_eq_zero.mpr (by simpa only [lift_algebraMap] using h (algebraMap A S x))
  · intro h
    have hh:(IsLocalRing.residue S).comp (lift P S e he).toRingHom=IsLocalRing.residue S:=by
      apply IsLocalization.ringHom_ext P.primeCompl
      ext x
      change IsLocalRing.residue S (lift P S e he (algebraMap A S x))=
        IsLocalRing.residue S (algebraMap A S x)
      rw [lift_algebraMap]
      apply sub_eq_zero.mp
      rw [←map_sub,←map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff S P (e x-x)).mpr (h x))
    intro x
    exact RingHom.congr_fun hh x

/-- This is the induced automorphism of the actual local residue field. -/
theorem residue_equiv_identity_iff:
    IsLocalRing.ResidueField.mapEquiv (lift P S e he)=RingEquiv.refl _ ↔
      ∀x:A,e x-x∈P:=by
  rw [←residue_trivial_iff P S e he]
  constructor
  · intro h x
    have hx:=congrArg (fun f:IsLocalRing.ResidueField S≃+*IsLocalRing.ResidueField S=>
      f (IsLocalRing.residue S x)) h
    simpa only [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue,RingEquiv.refl_apply,RingEquiv.coe_toRingHom] using hx
  · intro h
    ext y
    obtain ⟨x,rfl⟩:=IsLocalRing.residue_surjective y
    simpa only [IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue,RingEquiv.refl_apply,RingEquiv.coe_toRingHom] using h x
end PrimeLocalizationInertia318
