module
public import ContactOverlapAlgebraMaps318
public section
noncomputable section
namespace InfinityDenominatorOverlap318
open Polynomial ContactOverlapAlgebraMaps318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma cleared_product {S:Type*} [CommRing S] (b k U T:S) (a v:Fin 3→S)
    (hk:b*k=1) (h:U^2*T=b):
    b^7*(∏j,v j*k*(1-a j*k*U^2))=
      (∏j,v j)*U^8*(T*∏j,(T-a j)):=by
  have hf (j:Fin 3):b^2*(v j*k*(1-a j*k*U^2))=v j*U^2*(T-a j):=by
    calc
      _=v j*(b*(b*k)-a j*U^2*(b*k)^2):=by ring
      _=v j*U^2*(T-a j):=by rw [hk,←h];ring
  have hp:=congrArg (fun f:Fin 3→S=>∏j,f j) (funext hf)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
  calc
    _=b*((b^2)^3*(∏j,v j*k*(1-a j*k*U^2))):=by ring
    _=b*((∏j,v j)*(U^2)^3*(∏j,(T-a j))):=by
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        congrArg (fun x=>b*x) hp
    _=(∏j,v j)*U^8*(T*∏j,(T-a j)):=by rw [←h];ring

variable (c:Fin 4→ℚˣ)
@[expose] def denominator:Source c:=infinityMap c
  (algebraMap ℚ[X] (Infinity c) (InfinityOpenChart318.denominator c))
@[expose] def quartic:Source c:=
  SourceOpenFractionField318.orderToOpen c (SourceOpenFractionField318.d c)

lemma coefficient_image (j:Fin 3):
    infinityMap c (algebraMap ℚ[X] (Infinity c) (InfinityParameters318.coefficient c j))=
      algebraMap ℚ (Source c) (c j.succ:ℚ)*algebraMap ℚ (Source c) (↑(c 0)⁻¹:ℚ)*
        (1-algebraMap ℚ (Source c) (InfinityParameters318.contact j)*
          algebraMap ℚ (Source c) (↑(c 0)⁻¹:ℚ)*(SourceInfinityOverlap318.u c)^2):=by
  rw [InfinityParameters318.coefficient_shape]
  simp only [map_mul,map_sub,map_one,map_pow]
  have hC (q:ℚ):infinityMap c (algebraMap ℚ[X] (Infinity c) (C q))=
      algebraMap ℚ (Source c) q:=by
    rw [show algebraMap ℚ[X] (Infinity c) (C q)=algebraMap ℚ (Infinity c) q from
      (IsScalarTower.algebraMap_apply ℚ ℚ[X] (Infinity c) q).symm]
    exact (infinityMap c).commutes q
  rw [hC,hC]
  change _*(1-_*SourceInfinityOverlap318.u c^2)=_
  simp only [div_eq_mul_inv,map_mul,Units.val_inv_eq_inv_val]

lemma denominator_image :denominator c=
    ∏j:Fin 3,algebraMap ℚ (Source c) (c j.succ:ℚ)*algebraMap ℚ (Source c) (↑(c 0)⁻¹:ℚ)*
      (1-algebraMap ℚ (Source c) (InfinityParameters318.contact j)*
        algebraMap ℚ (Source c) (↑(c 0)⁻¹:ℚ)*(SourceInfinityOverlap318.u c)^2):=by
  change infinityMap c (algebraMap ℚ[X] (Infinity c) (∏j:Fin 3,InfinityParameters318.coefficient c j))=_
  simp only [map_prod,coefficient_image]

lemma quartic_image :quartic c=SourceInfinityOverlap318.t c*
    ∏j:Fin 3,(SourceInfinityOverlap318.t c-algebraMap ℚ (Source c) (InfinityParameters318.contact j)):=by
  rw [quartic,SourceOpenFractionField318.d,SourceOpenFractionField318.orderToOpen_on_polynomial]
  change algebraMap ℚ[X] (Source c) ContactKummerOrder318.denominator=_
  change algebraMap ℚ[X] (Source c) (∏i:Fin 4,(X-C (LinearContactSquareclass318.contacts i)))=_
  rw [Fin.prod_univ_succ,map_mul,map_prod]
  simp only [map_sub,show LinearContactSquareclass318.contacts 0=0 from rfl,map_zero,C_0,sub_zero]
  rfl

/-- The exact transported infinity denominator identity on the entire actual
common open, retaining all twist powers and the specified u=c₀/y₀ convention. -/
theorem denominator_identity :
    (algebraMap ℚ (Source c) (c 0:ℚ))^7*denominator c=
      algebraMap ℚ (Source c) (∏j:Fin 3,(c j.succ:ℚ))*
        (SourceInfinityOverlap318.u c)^8*quartic c:=by
  rw [denominator_image,quartic_image,map_prod]
  apply cleared_product
  · rw [←map_mul,Units.mul_inv,map_one]
  · exact SourceInfinityOverlap318.coordinate_relation c
end InfinityDenominatorOverlap318
