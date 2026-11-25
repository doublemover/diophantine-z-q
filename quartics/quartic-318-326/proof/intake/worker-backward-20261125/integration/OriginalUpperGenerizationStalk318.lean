module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public section
noncomputable section
namespace OriginalUpperGenerizationStalk318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {S : Scheme.{u}} (x : S)
abbrev A := S.presheaf.stalk x
abbrev F := S.fromSpecStalk x
variable (p : Spec (A x))
abbrev y := F x p
theorem specializes : y x p ⤳ x :=
  (show y x p ∈ {z : S | z ⤳ x} from Scheme.range_fromSpecStalk (X:=S) (x:=x) ▸ Set.mem_range_self p)
abbrev α : A x ⟶ S.presheaf.stalk (y x p) := S.presheaf.stalkSpecializes (specializes x p)
abbrev β := (F x).stalkMap p
abbrev B := (Spec (A x)).presheaf.stalk p

/-- The maps are maps of the real surface and its actual localization.
This identity uses monicity of Spec O_x → X, not equality of representatives. -/
theorem factor : α x p ≫ β x p=StructureSheaf.toStalk (A x) p := by
  apply Spec.map_injective
  apply (cancel_mono (F x)).mp
  rw [Spec.map_comp,Category.assoc,Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk,←Spec.fromSpecStalk_eq']

variable [IsIntegral S]
theorem field_apply (a : A x) : algebraMap (S.presheaf.stalk (y x p)) S.functionField ((α x p) a)=
    algebraMap (A x) S.functionField a := by
  change (S.presheaf.stalkSpecializes _) ((S.presheaf.stalkSpecializes _) a)=_
  rw [←ConcreteCategory.comp_apply,TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- The stalk of Spec O_x at p IS the ambient surface stalk at the same
generization y. The residue map is not just surjective: its injectivity
is proved using common generic meromorphic functions. -/
theorem bijective : Function.Bijective (β x p) := by
  let A' := A x
  let C' := S.presheaf.stalk (y x p)
  let K := S.functionField
  let : Algebra A' (B x p) := StructureSheaf.stalkAlgebra _ _
  let : IsLocalization.AtPrime (B x p) p.asIdeal := StructureSheaf.IsLocalization.to_stalk _ p
  have hinj : Function.Injective (StructureSheaf.toStalk A' p) :=
    IsLocalization.injective (B x p) p.asIdeal.primeCompl_le_nonZeroDivisors
  refine ⟨(RingHom.injective_iff_ker_eq_bot _).mpr ?_,(F x).stalkMap_surjective p⟩
  apply le_antisymm _ bot_le
  intro z hz
  change (β x p) z=0 at hz
  change z=0
  obtain ⟨a,b,hh,hab⟩ := IsFractionRing.div_surjective A' (algebraMap C' K z)
  have h : (α x p) a=(α x p) b*z := by
    apply IsFractionRing.injective C' K
    rw [map_mul,field_apply,field_apply]
    have hbb := (map_ne_zero_iff _ (IsFractionRing.injective A' K)).mpr (nonZeroDivisors.ne_zero hh)
    exact ((div_eq_iff hbb).mp hab).trans (mul_comm _ _)
  have h0 : a=0 := hinj (by
    change (StructureSheaf.toStalk A' p).hom a=(StructureSheaf.toStalk A' p).hom 0
    rw [map_zero,←factor]
    change (β x p).hom ((α x p).hom a)=0
    calc
      _ = (β x p).hom ((α x p).hom b*z) := congrArg (β x p).hom h
      _ = (β x p).hom ((α x p).hom b)*(β x p).hom z := map_mul _ _ _
      _ = _ := by simpa only [mul_zero] using congrArg ((β x p).hom ((α x p).hom b)*·) hz)
  apply IsFractionRing.injective C' K
  rw [map_zero,←hab,h0,map_zero,zero_div]

end OriginalUpperGenerizationStalk318
#print axioms OriginalUpperGenerizationStalk318.bijective
