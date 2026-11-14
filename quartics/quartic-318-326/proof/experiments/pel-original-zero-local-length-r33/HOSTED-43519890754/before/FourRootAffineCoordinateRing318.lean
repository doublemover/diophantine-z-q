module
public import FourRootCompletedComplexAtlas318
public import AffineEquationFunctor318
public section
noncomputable section
namespace FourRootAffineCoordinateRing318
open MvPolynomial FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ)

/-- Independent coordinate ring of the literal finite four-root equations.
The base variable is none; the four actual root variables are some k. -/
@[expose] def equation (k:Fin 4):MvPolynomial (Option (Fin 4)) ℂ:=
  X (some k)^2-X none+C (b k)
abbrev Ring:=MvPolynomial (Option (Fin 4)) ℂ ⧸ Ideal.span (Set.range (equation b))
@[expose] def coordinate (k:Option (Fin 4)):Ring b:=Ideal.Quotient.mk _ (X k)

lemma relation (k:Fin 4):coordinate b (some k)^2=coordinate b none-algebraMap ℂ (Ring b) (b k):=by
  have h:Ideal.Quotient.mk (Ideal.span (Set.range (equation b))) (equation b k)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k,rfl⟩)
  simp only [equation,map_add,map_sub,map_pow] at h
  change coordinate b (some k)^2-coordinate b none+algebraMap ℂ (Ring b) (b k)=0 at h
  linear_combination h

/-- Evaluation in any actual complex algebra retains all branch points. -/
@[expose] def lift {S:Type*} [CommRing S] [Algebra ℂ S]
    (t:S) (z:Fin 4→S) (hz:∀k,z k^2=t-algebraMap ℂ S (b k)):Ring b→ₐ[ℂ]S:=
  Ideal.Quotient.liftₐ _ (aeval (fun k => Option.elim k t z)) (by
    have hk:Ideal.span (Set.range (equation b))≤
        RingHom.ker (aeval (fun k => Option.elim k t z):MvPolynomial (Option (Fin 4)) ℂ→ₐ[ℂ]S):=by
      apply Ideal.span_le.mpr
      rintro _ ⟨k,rfl⟩
      change aeval (fun k => Option.elim k t z) (equation b k)=0
      simp [equation,hz]
    intro f hf
    exact hk hf)

@[simp] theorem lift_coordinate {S:Type*} [CommRing S] [Algebra ℂ S]
    (t:S) (z:Fin 4→S) (hz) (k:Option (Fin 4)):
    lift b t z hz (coordinate b k)=Option.elim k t z:=by
  simp [lift,coordinate,Ideal.Quotient.lift_mk]

theorem hom_ext {S:Type*} [CommRing S] [Algebra ℂ S]
    {f g:Ring b→ₐ[ℂ]S} (h:∀k,f (coordinate b k)=g (coordinate b k)):f=g:=by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

@[expose] def point (f:Ring b→ₐ[ℂ]ℂ):FinitePoints b:=
  ⟨(f (coordinate b none),fun k=>f (coordinate b (some k))),by
    intro k
    have h:=congrArg f (relation b k)
    simpa only [map_pow,map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply] using h⟩

/-- All complex-valued algebra points. This is not a claim that every
topological spectrum point is complex-valued. -/
@[expose] def pointEquiv:(Ring b→ₐ[ℂ]ℂ)≃FinitePoints b where
  toFun:=point b
  invFun p:=lift b p.val.1 p.val.2 (by simpa using p.property)
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
end FourRootAffineCoordinateRing318
