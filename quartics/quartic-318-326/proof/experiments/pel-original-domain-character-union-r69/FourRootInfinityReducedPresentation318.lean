module
public import FourRootInfinityDomain318
public section
noncomputable section
namespace FourRootInfinityReducedPresentation318
open MvPolynomial Algebra
variable (b:Fin 4→ℂ)

/-- Three independent equations after algebraically eliminating s0=1.
The naive five-equation presentation has a redundant equation and cannot
be used as a nonsingular five-by-five Jacobian presentation. -/
@[expose] def equation (k:Fin 3):MvPolynomial (Fin 4) ℂ:=
  X k.succ^2-1-C (b 0-b k.succ)*X 0^2
abbrev Ring:=MvPolynomial (Fin 4) ℂ ⧸ Ideal.span (Set.range (equation b))
@[expose] def coordinate (k:Fin 4):Ring b:=Ideal.Quotient.mk _ (X k)
lemma relation (k:Fin 3):coordinate b k.succ^2=
    1+algebraMap ℂ (Ring b) (b 0-b k.succ)*coordinate b 0^2:=by
  have h:Ideal.Quotient.mk (Ideal.span (Set.range (equation b))) (equation b k)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k,rfl⟩)
  simp only [equation,map_sub,map_pow,map_mul,map_one] at h
  change coordinate b k.succ^2-1-algebraMap ℂ (Ring b) (b 0-b k.succ)*coordinate b 0^2=0 at h
  linear_combination h

@[expose] def lift {S:Type*} [CommRing S] [Algebra ℂ S]
    (x:Fin 4→S) (hx:∀k:Fin 3,x k.succ^2=1+algebraMap ℂ S (b 0-b k.succ)*x 0^2):Ring b→ₐ[ℂ]S:=
  Ideal.Quotient.liftₐ _ (aeval x) (by
    have hk:Ideal.span (Set.range (equation b))≤RingHom.ker (aeval x:MvPolynomial (Fin 4) ℂ→ₐ[ℂ]S):=by
      apply Ideal.span_le.mpr
      rintro _ ⟨k,rfl⟩
      change aeval x (equation b k)=0
      simp [equation,hx]
    exact fun _ hf=>hk hf)
@[simp] theorem lift_coordinate {S:Type*} [CommRing S] [Algebra ℂ S]
    (x:Fin 4→S) (hx) (k:Fin 4):lift b x hx (coordinate b k)=x k:=by
  simp [lift,coordinate,Ideal.Quotient.lift_mk]
theorem hom_ext {S:Type*} [CommRing S] [Algebra ℂ S]
    {f g:Ring b→ₐ[ℂ]S} (h:∀k,f (coordinate b k)=g (coordinate b k)):f=g:=by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

@[expose] def originalCoordinate:Fin 4→FourRootInfinityCoordinateRing318.Ring b:=
  Fin.cases (FourRootInfinityCoordinateRing318.coordinate b none)
    (fun k=>FourRootInfinityCoordinateRing318.coordinate b (some k.succ))
@[expose] def toOriginal:Ring b→ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b:=
  lift b (originalCoordinate b) (fun k=>FourRootInfinityCoordinateRing318.relation b k.succ)
@[expose] def fromOriginal:FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]Ring b:=
  FourRootInfinityCoordinateRing318.lift b (coordinate b 0)
    (Fin.cases 1 (fun k=>coordinate b k.succ)) rfl (by
      intro k
      refine Fin.cases ?_ (fun j=>?_) k
      · simp
      · exact relation b j)
@[simp] theorem toOriginal_coordinate (k:Fin 4):
    toOriginal b (coordinate b k)=originalCoordinate b k:=lift_coordinate _ _ _ _
@[simp] theorem fromOriginal_base:fromOriginal b (FourRootInfinityCoordinateRing318.coordinate b none)=coordinate b 0:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _
@[simp] theorem fromOriginal_root (k:Fin 4):
    fromOriginal b (FourRootInfinityCoordinateRing318.coordinate b (some k))=
      Fin.cases 1 (fun j=>coordinate b j.succ) k:=
  FourRootInfinityCoordinateRing318.lift_coordinate _ _ _ _ _ _

@[expose] def equivalence:Ring b≃ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b:=
  AlgEquiv.ofAlgHom (toOriginal b) (fromOriginal b)
    (by
      apply FourRootInfinityCoordinateRing318.hom_ext
      intro k
      cases k with
      | none=>simp [AlgHom.comp_apply,originalCoordinate]
      | some k=>
        refine Fin.cases ?_ (fun j=>?_) k
        · simp [AlgHom.comp_apply,FourRootInfinityCoordinateRing318.zero_relation]
        · simp [AlgHom.comp_apply,originalCoordinate])
    (by
      apply hom_ext
      intro k
      refine Fin.cases ?_ (fun j=>?_) k
      · simp [AlgHom.comp_apply,originalCoordinate]
      · simp [AlgHom.comp_apply,originalCoordinate])

@[expose] def reducedPresentation:PreSubmersivePresentation ℂ (Ring b) (Fin 4) (Fin 3):=
  PreSubmersivePresentation.naive (v:=equation b) Fin.succ Fin.succ_injective
@[expose] def presentation:PreSubmersivePresentation ℂ
    (FourRootInfinityCoordinateRing318.Ring b) (Fin 4) (Fin 3):=
  (reducedPresentation b).ofAlgEquiv (equivalence b)

/-- True three-by-three Jacobian on the SAME original infinity quotient,
not a determinant formed from the redundant fifth equation. -/
theorem jacobian_formula:(presentation b).jacobian=
    8*∏k:Fin 3,FourRootInfinityCoordinateRing318.coordinate b (some k.succ):=by
  rw [presentation,PreSubmersivePresentation.jacobian_ofAlgEquiv]
  have he:(reducedPresentation b).jacobian=8*∏k:Fin 3,coordinate b k.succ:=by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [reducedPresentation,PreSubmersivePresentation.jacobiMatrix_naive,
      equation,Matrix.det_fin_three,coordinate,Fin.prod_univ_succ]
    <;> ring
  rw [he,map_mul,map_ofNat,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact toOriginal_coordinate b k.succ
end FourRootInfinityReducedPresentation318
