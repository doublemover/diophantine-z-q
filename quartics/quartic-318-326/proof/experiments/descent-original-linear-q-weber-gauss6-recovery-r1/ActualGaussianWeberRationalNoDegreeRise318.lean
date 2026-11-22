module
public import ActualGaussianWeberPrimitiveRational318
public import Mathlib.FieldTheory.RatFunc.Basic
public section
noncomputable section

namespace ActualGaussianWeberRationalNoDegreeRise318

open IsLocalRing Polynomial
open ActualGaussianWeberPrimitiveRational318

variable {K : Type*} [Field K] (V : ValuationSubring K)

private theorem rational_cross {L : Type*} [Field L] {a b c d : L[X]}
    (hb : b≠0) (hd : d≠0) (h : a*d=b*c) : RatFunc.mk a b=RatFunc.mk c d := by
  have hI := RatFunc.algebraMap_injective L
  have hB : algebraMap L[X] (RatFunc L) b≠0 :=
    fun he => hb (hI (he.trans (map_zero _).symm))
  have hD : algebraMap L[X] (RatFunc L) d≠0 :=
    fun he => hd (hI (he.trans (map_zero _).symm))
  rw [RatFunc.mk_eq_div,RatFunc.mk_eq_div]
  apply (div_eq_div_iff hB hD).2
  simpa only [map_mul,mul_comm] using congrArg (algebraMap L[X] (RatFunc L)) h

/-- An integral numerator and denominator for a function on the
two-dimensional Weierstrass generic chart, in the basis 1 and Y.
The two crossed identities are the exact two coefficient equations
for A⋅D=B⋅C; the residual denominator is nonzero in at least one
coefficient.  This package does not assume primitive normalization of A,B. -/
structure FinitePresentation (A B : K[X]) where
  c₀ : V[X]
  c₁ : V[X]
  d₀ : V[X]
  d₁ : V[X]
  cross₀ : A*d₀.map V.subtype=B*c₀.map V.subtype
  cross₁ : A*d₁.map V.subtype=B*c₁.map V.subtype
  finite : d₀.map (residue V)≠0 ∨ d₁.map (residue V)≠0

private theorem normalized_cross {A B : K[X]} (T : PrimitivePair V A B)
    (c d : V[X]) (h : A*d.map V.subtype=B*c.map V.subtype) : T.num*d=T.den*c := by
  apply Polynomial.map_injective V.subtype V.subtype_injective
  rw [Polynomial.map_mul,Polynomial.map_mul]
  apply mul_left_cancel₀ (C_ne_zero.mpr T.scale_ne)
  calc
    C T.scale*(T.num.map V.subtype*d.map V.subtype) = A*d.map V.subtype := by
      rw [←mul_assoc,T.num_eq]
    _ = B*c.map V.subtype := h
    _ = C T.scale*(T.den.map V.subtype*c.map V.subtype) := by
      rw [←mul_assoc,T.den_eq]

theorem reduced_cross {A B : K[X]} (T : PrimitivePair V A B)
    (c d : V[X]) (h : A*d.map V.subtype=B*c.map V.subtype) :
    (T.num.map (residue V))*(d.map (residue V)) =
      (T.den.map (residue V))*(c.map (residue V)) := by
  have e := congrArg (Polynomial.map (residue V)) (normalized_cross V T c d h)
  simpa only [Polynomial.map_mul] using e

private theorem denominator_survives {A B : K[X]} (T : PrimitivePair V A B)
    (G : FinitePresentation V A B) : T.den.map (residue V)≠0 := by
  intro hb
  have hn : T.num.map (residue V)=0 := by
    rcases G.finite with h₀|h₁
    · have e := reduced_cross V T G.c₀ G.d₀ G.cross₀
      rw [hb,zero_mul] at e
      exact (mul_eq_zero.mp e).resolve_right h₀
    · have e := reduced_cross V T G.c₁ G.d₁ G.cross₁
      rw [hb,zero_mul] at e
      exact (mul_eq_zero.mp e).resolve_right h₁
  exact T.some_nonzero_reduction.elim (fun h => h hn) (fun h => h hb)

/-- Actual Gauss no-degree-rise principle in the rational x-coordinate:
joint scale does not change A/B, the finite-place denominator cannot
vanish after specialization, and both polynomial degrees stay within
their original caps.  All finite integral coefficient representatives
give the same reduced rational element, by the two crossed equations. -/
theorem specialize_without_degree_rise (A B : K[X]) (hB : B≠0)
    (G : FinitePresentation V A B) :
    ∃ (T : PrimitivePair V A B),
      (T.den.map (residue V)≠0) ∧
      (T.num.map (residue V)).natDegree≤A.natDegree ∧
      (T.den.map (residue V)).natDegree≤B.natDegree ∧
      RatFunc.mk (T.num.map V.subtype) (T.den.map V.subtype)=RatFunc.mk A B ∧
      (∀ c d : V[X], A*d.map V.subtype=B*c.map V.subtype → d.map (residue V)≠0 →
        RatFunc.mk (T.num.map (residue V)) (T.den.map (residue V))=
          RatFunc.mk (c.map (residue V)) (d.map (residue V))) := by
  obtain ⟨T⟩ := primitive_pair V A B hB
  have hd := denominator_survives V T G
  have hg : T.den.map V.subtype≠0 := by
    intro e
    apply hB
    rw [←T.den_eq,e,mul_zero]
  refine ⟨T,hd,natDegree_map_le.trans T.num_degree,natDegree_map_le.trans T.den_degree,?_,?_⟩
  · apply rational_cross hg hB
    rw [←T.num_eq,←T.den_eq]
    ring
  · intro c d h hn
    exact rational_cross hd hn (reduced_cross V T c d h)

end ActualGaussianWeberRationalNoDegreeRise318
