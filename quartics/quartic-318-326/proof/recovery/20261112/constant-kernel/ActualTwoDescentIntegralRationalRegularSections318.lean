module
public import ActualTwoDescentFractionalLineStabilizerRegularity318
public section
noncomputable section
namespace ActualTwoDescentIntegralRationalRegularSections318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentRationalSectionLocalData318 ActualTwoDescentRationalSectionPointImages318
open ActualTwoDescentIntegralGenericSectionMaps318
universe u
variable (X : Scheme.{u}) [IsIntegral X]
/-- The literal structure sheaf embedded in its native generic stalk. -/
def model : RationalModel (ClutchedModule318.unit X) X.functionField where
  rho U hU s := by letI := hU; exact X.germToFunctionField U s
  injective U hU := by letI := hU; exact X.germToFunctionField_injective U
  natural U V hU hV h s := by
    letI := hU
    letI := hV
    exact germ_restrict h s
/-- Every actual stalk element has a genuine section representative;
thus this intrinsic image is EXACTLY the actual stalk-to-field range. -/
lemma point_image (x : X) (f : X.functionField) :
    f∈pointImage (model X) x ↔ ∃ r : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField r=f := by
  constructor
  · rintro ⟨U,hU,s,hx,hs⟩
    letI := hU
    refine ⟨X.presheaf.germ U x hx s,?_⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    exact hs
  · rintro ⟨r,hr⟩
    obtain ⟨U,hx,s,hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    letI : Nonempty U := ⟨⟨x,hx⟩⟩
    refine ⟨U,inferInstance,s,hx,?_⟩
    change X.germToFunctionField U s=f
    have hg : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s)=
        X.germToFunctionField U s := by rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    exact hg.symm.trans ((congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hs).trans hr)
local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X,trivial⟩⟩
/-- Full all-point regularity yields an ACTUAL global regular function,
by old native sheaf gluing; not a definition of a regular function. -/
lemma global_regular (f : X.functionField)
    (hf : ∀ x : X,∃ r : X.presheaf.stalk x,algebraMap _ X.functionField r=f) :
    ∃ s : Γ(X,⊤),X.germToFunctionField ⊤ s=f := by
  apply (image_iff_all_points (model X) ⊤ inferInstance f).mpr
  intro x
  exact (point_image X x.val f).mpr (hf x.val)
/-- BOTH regularity directions produce a genuine unit of the actual
native global-section ring with the specified generic value. -/
lemma global_unit (a : X.functionFieldˣ)
    (ha : ∀ x : X,(∃ r : X.presheaf.stalk x,algebraMap _ X.functionField r=(a:X.functionField)) ∧
      (∃ r : X.presheaf.stalk x,algebraMap _ X.functionField r=(↑a⁻¹:X.functionField))) :
    ∃ s : Γ(X,⊤)ˣ, X.germToFunctionField ⊤ (s:Γ(X,⊤))=(a:X.functionField) := by
  obtain ⟨s,hs⟩ := global_regular X (a:X.functionField) (fun x => (ha x).1)
  obtain ⟨t,ht⟩ := global_regular X (↑a⁻¹:X.functionField) (fun x => (ha x).2)
  have hst : s*t=1 := by
    apply X.germToFunctionField_injective ⊤
    rw [map_mul,hs,ht,map_one]
    exact a.val_inv
  refine ⟨⟨s,t,hst,?_⟩,hs⟩
  simpa only [mul_comm] using hst

end ActualTwoDescentIntegralRationalRegularSections318
