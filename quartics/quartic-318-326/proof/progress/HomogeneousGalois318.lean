module
public import ProjectiveGalois318
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public section
noncomputable section
namespace HomogeneousGalois318
open MvPolynomial ProjectiveGalois318
set_option maxHeartbeats 0
variable {F E ι κ:Type*} [Field F] [Field E] [Algebra F E]

/-- Actual homogeneous polynomial evaluation respects scaling by its degree.
No scalar-equivariance of the defining equations is supplied. -/
theorem eval₂_scale (p:MvPolynomial ι F) (n:ℕ) (hp:p.IsHomogeneous n)
    (x:ι→E) (c:E) :
    p.eval₂ (algebraMap F E) (fun i=>c*x i)=c^n*p.eval₂ (algebraMap F E) x := by
  classical
  simp only [eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,←hp.degree_eq_sum_deg_support hd]
  ring

/-- The rational normalized coordinates satisfy the actual original homogeneous
polynomial equations. The conclusion follows from field-map injectivity and
derived homogeneous scaling, rather than a separate curve-membership premise. -/
theorem rational_equations_of_scaled (p:MvPolynomial ι F) (n:ℕ)
    (hp:p.IsHomogeneous n) (x:ι→E) (y:ι→F) (c:E)
    (hcoord:∀i,algebraMap F E (y i)=c*x i)
    (hx:p.eval₂ (algebraMap F E) x=0) : p.eval y=0 := by
  apply (algebraMap F E).injective
  rw [map_zero]
  have hmap:algebraMap F E (p.eval y)=
      p.eval₂ (algebraMap F E) (fun i=>algebraMap F E (y i)) := by
    simpa [Function.comp_def] using (MvPolynomial.eval₂_comp_left (algebraMap F E)
      (RingHom.id F) y p)
  rw [hmap]
  simp_rw [hcoord]
  rw [eval₂_scale p n hp,hx,mul_zero]

/-- Actual Galois-fixed projective coordinates descend together with every
homogeneous equation over the base field. There is no finite-list restriction. -/
theorem equations_descend [FiniteDimensional F E] [IsGalois F E]
    (x:ι→E) (hx:x≠0) (polys:κ→MvPolynomial ι F) (degrees:κ→ℕ)
    (homogeneous:∀j,(polys j).IsHomogeneous (degrees j))
    (vanish:∀j,(polys j).eval₂ (algebraMap F E) x=0)
    (fixed:∀sigma:E≃ₐ[F]E,∃c:Eˣ,∀i,sigma (x i)=(c:E)*x i) :
    ∃(y:ι→F) (c:E),y≠0 ∧ c≠0 ∧
      (∀i,algebraMap F E (y i)=c*x i) ∧ (∀j,(polys j).eval y=0) := by
  obtain ⟨y,c,hy,hc,hcoord⟩:=normalized_coordinates x hx fixed
  refine ⟨y,c,hy,hc,hcoord,?_⟩
  intro j
  exact rational_equations_of_scaled (polys j) (degrees j) (homogeneous j)
    x y c hcoord (vanish j)

/-- Descent of an actual projective zero of a homogeneous system, including
both the actual base-change equality and the base-field defining equations. -/
theorem projective_zero_descend [FiniteDimensional F E] [IsGalois F E]
    (P:Projectivization E (ι→E))
    (polys:κ→MvPolynomial ι F) (degrees:κ→ℕ)
    (homogeneous:∀j,(polys j).IsHomogeneous (degrees j))
    (vanish:∀j,(polys j).eval₂ (algebraMap F E) P.rep=0)
    (fixed:∀sigma:E≃ₐ[F]E,Projectivization.map (automorphismMap sigma)
      (automorphismMap_injective sigma) P=P) :
    ∃(y:ι→F) (hy:y≠0),(∀j,(polys j).eval y=0) ∧
      Projectivization.map coordinateMap coordinateMap_injective
        (Projectivization.mk F y hy)=P := by
  have hs:∀sigma:E≃ₐ[F]E,∃c:Eˣ,∀i,sigma (P.rep i)=(c:E)*P.rep i:=by
    intro sigma
    apply scalar_of_projective_fixed P.rep (Projectivization.rep_nonzero P) sigma
    simpa only [Projectivization.mk_rep] using fixed sigma
  obtain ⟨y,c,hy,hc,hcoord,hzero⟩:=equations_descend P.rep
    (Projectivization.rep_nonzero P) polys degrees homogeneous vanish hs
  refine ⟨y,hy,hzero,?_⟩
  rw [Projectivization.map_mk,←Projectivization.mk_rep P]
  apply (Projectivization.mk_eq_mk_iff' E _ _ _ _).mpr
  refine ⟨c,?_⟩
  ext i
  exact (hcoord i).symm

end HomogeneousGalois318
