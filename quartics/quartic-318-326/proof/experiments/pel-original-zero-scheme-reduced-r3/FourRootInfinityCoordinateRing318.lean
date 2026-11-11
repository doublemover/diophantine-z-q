module
public import FourRootAffineCoordinateRing318
public section
noncomputable section
namespace FourRootInfinityCoordinateRing318
open MvPolynomial FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ)

/-- The normalized infinity ring retains s0=1. Without this equation the
wrong sixteen infinity signs would be introduced. -/
@[expose] def equation:Option (Fin 4)→MvPolynomial (Option (Fin 4)) ℂ
  | none=>X (some 0)-1
  | some k=>X (some k)^2-1-C (b 0-b k)*X none^2
abbrev Ring:=MvPolynomial (Option (Fin 4)) ℂ ⧸ Ideal.span (Set.range (equation b))
@[expose] def coordinate (k:Option (Fin 4)):Ring b:=Ideal.Quotient.mk _ (X k)

lemma zero_relation:coordinate b (some 0)=1:=by
  have h:Ideal.Quotient.mk (Ideal.span (Set.range (equation b))) (equation b none)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨none,rfl⟩)
  simpa only [equation,map_sub,map_one,sub_eq_zero,coordinate] using h

lemma relation (k:Fin 4):coordinate b (some k)^2=
    1+algebraMap ℂ (Ring b) (b 0-b k)*coordinate b none^2:=by
  have h:Ideal.Quotient.mk (Ideal.span (Set.range (equation b))) (equation b (some k))=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨some k,rfl⟩)
  simp only [equation,map_sub,map_pow,map_mul,map_one] at h
  change coordinate b (some k)^2-1-algebraMap ℂ (Ring b) (b 0-b k)*coordinate b none^2=0 at h
  linear_combination h

@[expose] def lift {S:Type*} [CommRing S] [Algebra ℂ S]
    (u:S) (s:Fin 4→S) (h0:s 0=1)
    (hs:∀k,s k^2=1+algebraMap ℂ S (b 0-b k)*u^2):Ring b→ₐ[ℂ]S:=
  Ideal.Quotient.liftₐ _ (aeval (Option.elim u s)) (by
    have hk:Ideal.span (Set.range (equation b))≤
        RingHom.ker (aeval (Option.elim u s):MvPolynomial (Option (Fin 4)) ℂ→ₐ[ℂ]S):=by
      apply Ideal.span_le.mpr
      rintro _ ⟨k,rfl⟩
      change aeval (Option.elim u s) (equation b k)=0
      cases k <;> simp [equation,h0,hs]
    intro f hf
    exact hk hf)

@[simp] theorem lift_coordinate {S:Type*} [CommRing S] [Algebra ℂ S]
    (u:S) (s:Fin 4→S) (h0) (hs) (k:Option (Fin 4)):
    lift b u s h0 hs (coordinate b k)=Option.elim u s k:=by
  simp [lift,coordinate,Ideal.Quotient.lift_mk]

theorem hom_ext {S:Type*} [CommRing S] [Algebra ℂ S]
    {f g:Ring b→ₐ[ℂ]S} (h:∀k,f (coordinate b k)=g (coordinate b k)):f=g:=by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

@[expose] def point (f:Ring b→ₐ[ℂ]ℂ):InfinityPoints b:=
  ⟨(f (coordinate b none),fun k=>f (coordinate b (some k))),by
    simpa only [map_one] using congrArg f (zero_relation b),by
    intro k
    have h:=congrArg f (relation b k)
    simpa only [map_pow,map_add,map_mul,map_one,AlgHom.commutes,algebraMap_self_apply] using h⟩

@[expose] def pointEquiv:(Ring b→ₐ[ℂ]ℂ)≃InfinityPoints b where
  toFun:=point b
  invFun p:=lift b p.val.1 p.val.2 p.property.1 (by simpa using p.property.2)
  left_inv f:=by
    apply hom_ext
    intro k
    cases k <;> simp [point]
  right_inv p:=by
    apply Subtype.ext
    apply Prod.ext
    · simp [point]
    · funext k
      simp [point]
end FourRootInfinityCoordinateRing318
