module
public import PELOriginalCoordinateGrowth318
public import HomogeneousRatioBox318
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public section
noncomputable section
namespace PELOriginalHomogeneousRatioDependence318
open scoped BigOperators
open CubicBoxMonomials318 HomogeneousRatioBox318
open PELOriginalGradedSectionRing318 PELOriginalCubicRelationIdeal318
open PELOriginalCoordinateGrowth318
variable (τ:ℂ)(hτ:0<τ.im)
/-- The actual homogenized box lands in ONE genuine coordinate piece,
which already injects into the FULL original H0(L^(9dm)). -/
@[expose] def boxImage(d m:ℕ)(B:Equations)(A:Fin 3→Equations)
    (hB:B.IsHomogeneous d)(hA:∀i,(A i).IsHomogeneous d):
    (Box m→ℂ)→ₗ[ℂ]degreePiece τ hτ (d*(3*m)):=
  ((presentation τ hτ).toLinearMap.comp (cleared B A m)).codRestrict _
    (fun c=>⟨cleared B A m c,cleared_homogeneous B A m hB hA c,rfl⟩)
lemma boxImage_injective {K:Type*}[Field K][Algebra ℂ K]
    (F:Ring τ hτ→ₐ[ℂ]K)(d m:ℕ)(B:Equations)(A:Fin 3→Equations)
    (hB:B.IsHomogeneous d)(hA:∀i,(A i).IsHomogeneous d)
    (hden:F (presentation τ hτ B)≠0)
    (hind:AlgebraicIndependent ℂ (fun i=>F (presentation τ hτ (A i))/F (presentation τ hτ B))):
    Function.Injective (boxImage τ hτ d m B A hB hA):=by
  intro c e h
  have hz:boxImage τ hτ d m B A hB hA (c-e)=0:=by rw [map_sub,h,sub_self]
  have hf:F (presentation τ hτ (cleared B A m (c-e)))=0:=by
    have hh:=congrArg (fun z:degreePiece τ hτ (d*(3*m))=>F z.val) hz
    change F (presentation τ hτ (cleared B A m (c-e)))=F 0 at hh
    simpa only [map_zero] using hh
  have hh:=cleared_evaluation B A m (F.comp (presentation τ hτ)) hden (c-e)
  change F (presentation τ hτ (cleared B A m (c-e)))=
    (F (presentation τ hτ B))^(3*m)*
      MvPolynomial.aeval (fun i=>F (presentation τ hτ (A i))/F (presentation τ hτ B))
        (polynomial m (c-e)) at hh
  rw [hf] at hh
  have he:=hind.eq_zero_of_aeval_eq_zero (polynomial m (c-e))
    ((mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hden))
  have hc:c-e=0:= (polynomial_injective m) (he.trans (map_zero (polynomial m)).symm)
  exact sub_eq_zero.mp hc
/-- Three ratios with a common positive-degree homogeneous denominator
CANNOT be algebraically independent in any field image of the actual
original section ring. The obstruction is the proved FULL H0 growth,
not an assumed Hilbert polynomial, dimension theorem, or Chow theorem. -/
theorem not_algebraicIndependent {K:Type*}[Field K][Algebra ℂ K]
    (F:Ring τ hτ→ₐ[ℂ]K)(d:ℕ)(hd:0<d)(B:Equations)(A:Fin 3→Equations)
    (hB:B.IsHomogeneous d)(hA:∀i,(A i).IsHomogeneous d)
    (hden:F (presentation τ hτ B)≠0):
    ¬AlgebraicIndependent ℂ
      (fun i=>F (presentation τ hτ (A i))/F (presentation τ hτ B)):=by
  intro hind
  let m:ℕ:=81*d^2
  have hm:0<m:=Nat.mul_pos (by decide) (pow_pos hd _)
  have hdeg:d*(3*m)≠0:=Nat.mul_ne_zero (Nat.ne_of_gt hd)
    (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))
  have hdim:(m+1)^3≤9*(d*(3*m))^2:=by
    calc
      (m+1)^3=Module.finrank ℂ (Box m→ℂ):=by
        rw [Module.finrank_fintype_fun_eq_card,CubicBoxMonomials318.card]
      _≤Module.finrank ℂ (degreePiece τ hτ (d*(3*m))):=
        LinearMap.finrank_le_finrank_of_injective
          (boxImage_injective τ hτ F d m B A hB hA hden hind)
      _≤9*(d*(3*m))^2:=by
        simpa only [if_neg hdeg] using whole_growth_bound τ hτ (d*(3*m))
  have he:9*(d*(3*m))^2=m^3:=by dsimp [m];ring
  rw [he] at hdim
  have hs:m^3<(m+1)^3:=by nlinarith [Nat.zero_le (m*m)]
  exact (not_lt_of_ge hdim) hs
/-- A genuine nonzero polynomial relation exists among those SAME
three ratios. No polynomial generators of the whole ideal are asserted. -/
theorem exists_relation {K:Type*}[Field K][Algebra ℂ K]
    (F:Ring τ hτ→ₐ[ℂ]K)(d:ℕ)(hd:0<d)(B:Equations)(A:Fin 3→Equations)
    (hB:B.IsHomogeneous d)(hA:∀i,(A i).IsHomogeneous d)
    (hden:F (presentation τ hτ B)≠0):
    ∃p:MvPolynomial (Fin 3) ℂ,p≠0∧
      MvPolynomial.aeval (fun i=>F (presentation τ hτ (A i))/F (presentation τ hτ B)) p=0:=by
  have h:=not_algebraicIndependent τ hτ F d hd B A hB hA hden
  rw [algebraicIndependent_iff] at h
  push_neg at h
  obtain ⟨p,hp,hne⟩:=h
  exact ⟨p,hne,hp⟩
end PELOriginalHomogeneousRatioDependence318
