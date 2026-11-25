module
public import OriginalUpperGenerizationStalk318

public section
noncomputable section
namespace OriginalUpperGenerizationField318

open AlgebraicGeometry CategoryTheory Order
open OriginalUpperGenerizationStalk318

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {S : Scheme.{u}} [IsIntegral S]
variable (x : S) (p : Spec (S.presheaf.stalk x))

/-- This prime's codimension in the ambient surface, not merely in an
independent affine chart. The proof uses the literal stalk map of the
canonical fromSpecStalk morphism. -/
theorem codimension : coheight (y x p) = p.asIdeal.height := by
  let e := RingEquiv.ofBijective (β x p).hom (bijective x p)
  have h :
      ringKrullDim (S.presheaf.stalk (y x p)) = ringKrullDim (B x p) :=
    Order.krullDim_eq_of_orderIso (PrimeSpectrum.comapEquiv e)
  let : Algebra (A x) (B x p) := StructureSheaf.stalkAlgebra _ p
  let : IsLocalization.AtPrime (B x p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ p
  rw [ringKrullDim_stalk_eq_coheight,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (B x p)] at h
  exact_mod_cast h

/-- Every actual regular function germ at the generization y is a
fraction in this literal closed stalk with denominator outside p.
The resulting map takes values in the exact SAME function field.
No abstract comparison of normalizations of valuations is required. -/
theorem fractions (z : S.presheaf.stalk (y x p)) :
    ∃ a : A x, ∃ s : p.asIdeal.primeCompl,
      algebraMap (S.presheaf.stalk (y x p)) S.functionField z =
        algebraMap (A x) S.functionField a / algebraMap (A x) S.functionField s := by
  let : Algebra (A x) (B x p) := StructureSheaf.stalkAlgebra _ p
  let : IsLocalization.AtPrime (B x p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ p
  let φ := (β x p).hom
  let ψ := (α x p).hom
  have hφ (a : A x) : φ (ψ a) = algebraMap (A x) (B x p) a :=
    congrArg (fun f : A x ⟶ B x p => f.hom a) (factor x p)
  obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj p.asIdeal.primeCompl (φ z)
  have hb : z * ψ s = ψ a := by
    apply (bijective x p).1
    change φ (z * ψ s) = φ (ψ a)
    rw [map_mul,hφ,hφ]
    exact hs
  refine ⟨a,s, (eq_div_iff ?_).mpr ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (A x) S.functionField)).mpr
      (fun h => s.property (h ▸ p.asIdeal.zero_mem))
  · have he := congrArg (algebraMap (S.presheaf.stalk (y x p)) S.functionField) hb
    rw [map_mul] at he
    rw [← field_apply x p (s : A x), ← field_apply x p a]
    exact he

end OriginalUpperGenerizationField318
#print axioms OriginalUpperGenerizationField318.codimension
#print axioms OriginalUpperGenerizationField318.fractions
