module
public import IdempotentFactor318
public section
noncomputable section
namespace EtaleDomainComponent318
open Algebra
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R B K:Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing B] [Nontrivial B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
  [Field K] [Algebra R K] [IsFractionRing R K]

include K in
/-- Every nonzero actual finite-etale cover of a normal domain contains an
actual idempotent-localized finite-etale domain component. -/
theorem exists_domain_component :
    ∃e:B, IsIdempotentElem e ∧ IsDomain (Localization.Away e) ∧
      Module.Finite R (Localization.Away e) ∧ Algebra.Etale R (Localization.Away e) := by
  classical
  let G:=B⊗[R]K
  letI:Algebra K G:=Algebra.TensorProduct.rightAlgebra
  have hinj:Function.Injective (algebraMap B G):=
    Algebra.TensorProduct.includeLeft_injective (S:=B) (IsFractionRing.injective R K)
  letI:Nontrivial G:=⟨⟨0,1,fun h=>zero_ne_one (hinj (by simpa only [map_zero,map_one] using h))⟩⟩
  let e0:(K⊗[R]B) ≃ₐ[K] G:=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with commutes':=by intro k;rfl }
  letI:Algebra.Etale K G:=Algebra.Etale.of_equiv e0
  obtain ⟨I,hI,L,hL,aL,E,hfin⟩:=(Algebra.Etale.iff_exists_algEquiv_prod K G).mp inferInstance
  letI:=hI
  letI:=hL
  letI:=aL
  have hi:Nonempty I:=by
    by_contra hi
    letI:IsEmpty I:=not_nonempty_iff.mp hi
    have h:(0:G)=1:=E.injective (Subsingleton.elim _ _)
    exact zero_ne_one h
  let i:I:=Classical.choice hi
  let x:G:=E.symm (Pi.single i 1)
  have hx:IsIdempotentElem x:=by
    change x*x=x
    apply E.injective
    simp only [map_mul,AlgEquiv.apply_symm_apply,x]
    ext j
    by_cases hj:j=i
    · subst j;simp
    · simp [hj]
  obtain ⟨e,⟨he,hee⟩,_⟩:=GenericIdempotent318.existsUnique_idempotent x hx
  let φ:B→+*∀j,L j:=E.toRingHom.comp (algebraMap B G)
  have hφe:φ e=Pi.single i 1:=by
    change E (algebraMap B G e)=_
    rw [hee]
    exact E.apply_symm_apply _
  have hφ:Function.Injective φ:=E.injective.comp hinj
  exact ⟨e,he,IdempotentFactor318.component_domain L φ i e he hφe hφ,
    IdempotentFactor318.component_finite e he R,
    IdempotentFactor318.component_etale e R⟩
end EtaleDomainComponent318
