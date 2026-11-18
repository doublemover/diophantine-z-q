module
public import PELOriginalCharacterUnramifiedCover318
public import PELOriginalRealBranchParameters318
public import PELOriginalNormalizedDoubleCover318
public section
noncomputable section
namespace PELOriginalHalfPlaneDoubleCover318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalNormalizedDoubleCover318 PELOriginalRealBranchParameters318

@[expose] def nonreal : Set (OnePoint ℂ):=((↑):ℂ→OnePoint ℂ) '' {z:ℂ | z.im≠0}
@[expose] def halfPlane (upper:Bool) : Set (OnePoint ℂ):=
  ((↑):ℂ→OnePoint ℂ) '' {z:ℂ | if upper then 0<z.im else z.im<0}

lemma nonreal_avoids_branches (i:Fin 4) (z:ℂ) (hz:z.im≠0) :
    ¬((z:OnePoint ℂ)=∞ ∨ (z:OnePoint ℂ)=(0:ℂ) ∨
      (z:OnePoint ℂ)=(1:ℂ) ∨ (z:OnePoint ℂ)=(branchParameter i:ℂ)) := by
  rintro (h|h|h|h)
  · exact OnePoint.coe_ne_infty z h
  · apply hz
    rw [OnePoint.coe_injective h]
    simp
  · apply hz
    rw [OnePoint.coe_injective h]
    simp
  · apply hz
    rw [OnePoint.coe_injective h,branchParameter_im_zero]

/-- Genuine covering over every nonreal target point, transported from
actual regular/omitted-inertia original charts through the SAME coordinate. -/
theorem covering_nonreal (i:Fin 4) : IsCoveringMapOn (normalizedMap i) nonreal := by
  have hc:=(PELOriginalCharacterUnramifiedCover318.covering_off_branch i).homeomorph_comp (coordinate i)
  apply hc.mono
  rintro p ⟨z,hz,rfl⟩ hbranch
  have hb:=(actual_branch_values i ((coordinate i).symm (z:OnePoint ℂ))).mp hbranch
  simp only [Homeomorph.apply_symm_apply] at hb
  exact nonreal_avoids_branches i z hz hb

lemma halfPlane_subset_nonreal (upper:Bool) : halfPlane upper⊆nonreal := by
  rintro p ⟨z,hz,rfl⟩
  refine ⟨z,?_,rfl⟩
  cases upper
  · exact (show z.im<0 from hz).ne
  · exact (show 0<z.im from hz).ne'

theorem halfPlane_covering (i:Fin 4) (upper:Bool) :
    IsCoveringMapOn (normalizedMap i) (halfPlane upper) :=
  (covering_nonreal i).mono (halfPlane_subset_nonreal upper)

/-- The source is the actual full inverse image, not a selected sheet. -/
abbrev Source (i:Fin 4) (upper:Bool):=(normalizedMap i) ⁻¹' halfPlane upper
@[expose] def projection (i:Fin 4) (upper:Bool) : Source i upper→halfPlane upper :=
  (halfPlane upper).restrictPreimage (normalizedMap i)

theorem actual_restricted_covering (i:Fin 4) (upper:Bool) :
    IsCoveringMap (projection i upper) :=
  (halfPlane_covering i upper).isCoveringMap_restrictPreimage

theorem actual_restricted_surjective (i:Fin 4) (upper:Bool) :
    Function.Surjective (projection i upper) := by
  intro z
  obtain ⟨x,hx⟩:=PELOriginalNormalizedDoubleCover318.surjective i z.val
  refine ⟨⟨x,hx.symm ▸ z.property⟩,?_⟩
  exact Subtype.ext hx

/-- Exact two-point fibers at EVERY point of either genuine half-plane.
This does not yet choose globally continuous sheets or identify two covers. -/
theorem halfPlane_fiber_two (i:Fin 4) (upper:Bool) (p:halfPlane upper) :
    Nat.card {x:CharacterBase i // normalizedMap i x=p.val}=2 := by
  obtain ⟨z,hz,hzp⟩:=halfPlane_subset_nonreal upper p.property
  rw [←hzp,all_fibers]
  exact if_neg (nonreal_avoids_branches i z hz)

@[expose] def restrictedFiberEquiv (i:Fin 4) (upper:Bool) (p:halfPlane upper) :
    {x:Source i upper // projection i upper x=p}≃
      {x:CharacterBase i // normalizedMap i x=p.val} where
  toFun x:=⟨x.val.val,congrArg Subtype.val x.property⟩
  invFun x:=⟨⟨x.val,x.property.symm ▸ p.property⟩,Subtype.ext x.property⟩
  left_inv x:=by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x:=rfl

theorem actual_restricted_fiber_two (i:Fin 4) (upper:Bool) (p:halfPlane upper) :
    Nat.card {x:Source i upper // projection i upper x=p}=2 := by
  rw [Nat.card_congr (restrictedFiberEquiv i upper p)]
  exact halfPlane_fiber_two i upper p
end PELOriginalHalfPlaneDoubleCover318
