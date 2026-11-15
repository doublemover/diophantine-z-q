module
public import WholeOpenLineFrame318
public import RelativeLineClassQuotient318
public import Mathlib.AlgebraicGeometry.Scheme
public section
noncomputable section
namespace FieldLineClassTrivial318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TopologicalSpace
universe u
variable (K : Type u) [Field K]
/-- The original finite open-frame cover of a field spectrum has a
member equal to the WHOLE scheme, since its underlying space is one point. -/
lemma exists_top_frame (L : Line (Spec (CommRingCat.of K))) : ∃ i,L.opens i=⊤ := by
  let x : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hx : x∈⨆ i,L.opens i := L.cover (show x∈(⊤ : (Spec (CommRingCat.of K)).Opens) from trivial)
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨i,le_antisymm le_top ?_⟩
  intro y hy
  simpa only [Subsingleton.elim y x] using hi
@[expose] def trivialization (L : Line (Spec (CommRingCat.of K))) :
    L.object ≅ SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf := by
  obtain ⟨i,hi⟩ := exists_top_frame K L
  have e : SheafOfModules.unit (⊤ : (Spec (CommRingCat.of K)).Opens).toScheme.ringCatSheaf ≅
      L.object.restrict (⊤ : (Spec (CommRingCat.of K)).Opens).ι := by
    rw [←hi]
    exact L.frame i
  exact (WholeOpenLineFrame318.iso L.object e).symm
lemma classOf_eq_one (L : Line (Spec (CommRingCat.of K))) : classOf L=1 :=
  (LineSheafUnit318.eq_unitClass_iff L).mpr ⟨trivialization K L⟩
lemma class_eq_one (c : Class (Spec (CommRingCat.of K))) : c=1 := by
  induction c using LineSheafClass318.induction with
  | h L => exact classOf_eq_one K L

/-- Over a field, the ACTUAL quotient by base lines loses no line-class
information. This concerns the naive relative quotient, not yet fppf
sheafification or representability. -/
lemma classMap_injective {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K)) :
    Function.Injective (RelativeLineClassQuotient318.classMap p) := by
  intro a b hab
  have h : RelativeLineClassQuotient318.classMap p (a*b⁻¹)=1 := by
    rw [map_mul,map_inv,hab,mul_inv_cancel]
  obtain ⟨d,hd⟩ := (RelativeLineClassQuotient318.classMap_eq_one_iff p _).mp h
  rw [class_eq_one K d,map_one] at hd
  exact mul_inv_eq_one.mp hd.symm
end FieldLineClassTrivial318
