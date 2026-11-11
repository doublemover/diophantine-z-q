module
public import PrincipalIdealOpenRestriction318
public import ReducedSourceClosedLift318
public section
noncomputable section
namespace PrincipalZeroComplexPoints318
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} (r : Γ(X,⊤))
open PrincipalIdealOpenRestriction318

/-- Underlying support is exactly the principal vanishing locus; this
statement does not alter the full principal ideal defining the scheme. -/
lemma range : Set.range (inclusion r)=(X.basicOpen r : Set X)ᶜ := by
  rw [inclusion,Scheme.IdealSheafData.range_subschemeι,principal,
    Scheme.IdealSheafData.coe_support_ofIdealTop,Scheme.zeroLocus_span,Scheme.zeroLocus_singleton]

lemma point_mem (p : Spec (CommRingCat.of ℂ) ⟶ X) :
    p (IsLocalRing.closedPoint ℂ) ∈ Set.range (inclusion r) ↔
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop r)=0 := by
  rw [range]
  change (IsLocalRing.closedPoint ℂ ∉ p ⁻¹ᵁ X.basicOpen r) ↔ _
  rw [Scheme.preimage_basicOpen_top]
  by_cases h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop r)=0
  · have hz : p.appTop r=0 := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
      (h.trans (map_zero _).symm)
    simp only [hz,Scheme.basicOpen_zero,SetLike.mem_coe,TopologicalSpace.Opens.mem_bot,
      not_false_eq_true,h,iff_self]
  · have hu : IsUnit (p.appTop r) := by
      have hv := (isUnit_iff_ne_zero.mpr h).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
      simpa only [Iso.hom_inv_id_apply] using hv
    rw [Scheme.basicOpen_of_isUnit _ hu]
    simpa only [SetLike.mem_coe,TopologicalSpace.Opens.mem_top,not_true_eq_false,false_iff] using h

/-- A vanishing genuine complex-valued point lifts to the full principal
zero scheme, not only to a chosen set of zero points. -/
@[expose] def point (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop r)=0) :
    Spec (CommRingCat.of ℂ) ⟶ zeroScheme r :=
  ReducedSourceClosedLift318.lift (inclusion r) p (by
    rintro x ⟨y,rfl⟩
    have hy : y=IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hy]
    exact (point_mem r p).mpr h)
@[reassoc] lemma point_inclusion (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (h : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop r)=0) :
    point r p h≫inclusion r=p := ReducedSourceClosedLift318.lift_fac _ _ _
end PrincipalZeroComplexPoints318
