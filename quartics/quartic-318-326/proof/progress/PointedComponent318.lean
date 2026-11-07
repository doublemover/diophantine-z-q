module
public import EtaleDomainComponent318
public section
noncomputable section
namespace PointedComponent318
open Algebra
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R B K Ω:Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω]

include K in
/-- The actual component can be chosen through a given field-valued point.
The generic idempotent partition and the point's factor are derived. -/
theorem exists_component_through (β:B→+*Ω) :
    ∃e:B, IsIdempotentElem e ∧ β e=1 ∧ IsDomain (Localization.Away e) ∧
      Module.Finite R (Localization.Away e) ∧ Algebra.Etale R (Localization.Away e) := by
  classical
  let G:=B⊗[R]K
  letI:Algebra K G:=Algebra.TensorProduct.rightAlgebra
  have hinj:Function.Injective (algebraMap B G):=
    Algebra.TensorProduct.includeLeft_injective (S:=B) (IsFractionRing.injective R K)
  let e0:(K⊗[R]B) ≃ₐ[K] G:=
    { (Algebra.TensorProduct.comm R K B).toRingEquiv with commutes':=by intro k;rfl }
  letI:Algebra.Etale K G:=Algebra.Etale.of_equiv e0
  obtain ⟨I,hI,L,hL,aL,E,hfin⟩:=(Algebra.Etale.iff_exists_algEquiv_prod K G).mp inferInstance
  letI:=hI;letI:=hL;letI:=aL
  letI:=Fintype.ofFinite I
  have desc:∀i:I,∃e:B,IsIdempotentElem e ∧ algebraMap B G e=E.symm (Pi.single i 1):=by
    intro i
    apply ExistsUnique.exists
    apply GenericIdempotent318.existsUnique_idempotent
    change E.symm (Pi.single i 1)*E.symm (Pi.single i 1)=E.symm (Pi.single i 1)
    apply E.injective
    simp only [map_mul,AlgEquiv.apply_symm_apply]
    ext j
    by_cases hji:j=i
    · subst j;simp
    · simp [hji]
  choose e he hee using desc
  have hsum:∑i,e i=1 := by
    apply hinj
    apply E.injective
    simp only [map_sum,map_one,hee,AlgEquiv.apply_symm_apply]
    ext j
    simp
  have hi:∃i,β (e i)≠0 := by
    by_contra hi
    push_neg at hi
    have hh:=congrArg β hsum
    simp only [map_sum,map_one,hi,Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  obtain ⟨i,hi⟩:=hi
  have hβ:β (e i)=1 := by
    apply mul_left_cancel₀ hi
    rw [mul_one,←map_mul]
    exact congrArg β (he i)
  let φ:B→+*∀j,L j:=E.toRingHom.comp (algebraMap B G)
  have hφe:φ (e i)=Pi.single i 1:=by
    change E (algebraMap B G (e i))=_
    rw [hee]
    exact E.apply_symm_apply _
  have hφ:Function.Injective φ:=E.injective.comp hinj
  exact ⟨e i,he i,hβ,IdempotentFactor318.component_domain L φ i (e i) (he i) hφe hφ,
    IdempotentFactor318.component_finite (e i) (he i) R,
    IdempotentFactor318.component_etale (e i) R⟩

end PointedComponent318
