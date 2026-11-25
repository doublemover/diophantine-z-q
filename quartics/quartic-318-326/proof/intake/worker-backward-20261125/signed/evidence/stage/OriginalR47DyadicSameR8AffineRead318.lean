module
public import OriginalR8ActualRetainedChiForHeight318
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public section
noncomputable section

namespace OriginalR47DyadicSameR8AffineRead318

open AlgebraicGeometry CategoryTheory Polynomial NumberField
open OriginalR8ExactMarkedReciprocal318 (χ)
open OriginalR8ActualRetainedChiForHeight318
open OriginalR8IntegralMarkedRead318 (CentreRead)
open OriginalUpperR60RetainedChiRead318 (retained retained_ambient)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {E V B D : Type u} [Field E] [Field V] [Algebra E[X] V] [Algebra (𝓞 E) V]
  [NumberField E] [Algebra E V] [IsScalarTower (𝓞 E) E V] [IsScalarTower E E[X] V]
  [CommRing B] [CommRing D]
variable (hχ : χ (E:=E) (V:=V) ≠ 0)
variable (n : ℕ) (full : CentreRead (E:=E) (V:=V) (n : 𝓞 E))
variable (L : Spec (CommRingCat.of B) ⟶ (U hχ).toScheme)

abbrev affinePull : CommRingCat.of ((𝓞 E)[X]) ⟶ CommRingCat.of B :=
  Spec.preimage (L ≫ coordinate hχ)

/-- The dyadic χ coefficient is literally X pulled back from the strict
actual normalized R8 affine chart. No separate arithmetic function. -/
abbrev scalar : B := (affinePull hχ L).hom Polynomial.X

include full in
/-- Specialize only at a point lying over the *whole* held original
section. This produces the hmark input of the exact dyadic axis test
by the closed-point map, not by assuming its scalar equality or
choosing a modular H orbit using that equality. D may be the further
proof trait, with its genuine map to the original coefficient base. -/
theorem residue_from_whole
    (β : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (𝓞 E)))
    (z : PrimeSpectrum B) (w : PrimeSpectrum D)
    (dyadic : (2 : 𝓞 E) ∈ (β w).asIdeal)
    (whole : (L ≫ (U hχ).ι) z =
      (β ≫ sameSection hχ (n : 𝓞 E) full) w) :
    (2 : B) ∈ z.asIdeal ∧
      Ideal.Quotient.mk z.asIdeal (scalar hχ L) = (n : B ⧸ z.asIdeal) := by
  let H := retained (sameSection hχ (n : 𝓞 E) full)
    (U hχ) (lands hχ (n : 𝓞 E) full)
  let a : ((𝓞 E)[X]) →+* 𝓞 E := Polynomial.evalRingHom (n : 𝓞 E)
  let f : CommRingCat.of ((𝓞 E)[X]) ⟶ CommRingCat.of B := affinePull hχ L
  have hU : L z = H (β w) := by
    apply ((U hχ).ι).isEmbedding.injective
    have hH := congrArg (fun j : Spec (CommRingCat.of (𝓞 E)) ⟶ source hχ => j (β w))
      (retained_ambient (sameSection hχ (n : 𝓞 E) full)
        (U hχ) (lands hχ (n : 𝓞 E) full))
    change ((U hχ).ι) (H (β w)) = sameSection hχ (n : 𝓞 E) full (β w) at hH
    rw [hH]
    simpa only [Scheme.Hom.comp_apply] using whole
  have hf : Spec.map f = L ≫ coordinate hχ := Spec.map_preimage _
  have hp : Spec.map f z = Spec.map (CommRingCat.ofHom a) (β w) := by
    rw [hf,Scheme.Hom.comp_apply,hU]
    change (H ≫ coordinate hχ) (β w) = _
    rw [entire_coordinate hχ (n : 𝓞 E) full]
  have hTwo : Polynomial.C (2 : 𝓞 E) ∈ (Spec.map (CommRingCat.ofHom a) (β w)).asIdeal := by
    change a (Polynomial.C (2 : 𝓞 E)) ∈ (β w).asIdeal
    simpa only [a,Polynomial.coe_evalRingHom,Polynomial.eval_C] using dyadic
  have hTwo' : f.hom (Polynomial.C (2 : 𝓞 E)) ∈ z.asIdeal := by
    rw [← hp] at hTwo
    exact hTwo
  have h₂ : (2 : B) ∈ z.asIdeal := by
    simpa only [map_ofNat] using hTwo'
  refine ⟨h₂,?_⟩
  let d : (𝓞 E)[X] := Polynomial.X - Polynomial.C (n : 𝓞 E)
  have hmem : d ∈ (Spec.map (CommRingCat.ofHom a) (β w)).asIdeal := by
    change a d ∈ (β w).asIdeal
    simp only [a,d,Polynomial.coe_evalRingHom,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,sub_self,Ideal.zero_mem]
  have hz : f.hom d ∈ z.asIdeal := by
    rw [← hp] at hmem
    exact hmem
  have hD : f.hom d = scalar hχ L - (n : B) := by
    simp only [d,map_sub,Polynomial.C_eq_natCast,map_natCast,f,scalar]
  rw [hD] at hz
  apply sub_eq_zero.mp
  rw [← map_natCast (Ideal.Quotient.mk z.asIdeal), ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr hz

end OriginalR47DyadicSameR8AffineRead318

#print axioms OriginalR47DyadicSameR8AffineRead318.residue_from_whole
