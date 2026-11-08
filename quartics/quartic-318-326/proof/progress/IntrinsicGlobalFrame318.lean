module
public import WeierstrassIntrinsicOverlaps318
public import IntrinsicChartFrames318
public import LocalSectionCompatibility318
public import InvariantNormalizedFrames318
public section
noncomputable section
namespace IntrinsicGlobalFrame318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open WeierstrassIntrinsicSections318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
inductive Chart where
  | x
  | finite
  | infinity

variable {R : Type u} [CommRing R] (A B : R)

@[expose] def opens (i : ULift.{u} Chart) : (WeierstrassGluing318.scheme A B).Opens :=
  match i.down with
  | .x => xOpen A B
  | .finite => finiteOpen A B
  | .infinity => infinityOpen A B

@[expose] def localSection (i : ULift.{u} Chart) :
    Γ(FamilyIntrinsicDifferentials318.familyOmega A B,opens A B i) :=
  match i with
  | ⟨.x⟩ => xSection A B
  | ⟨.finite⟩ => finiteSection A B
  | ⟨.infinity⟩ => infinitySection A B

theorem cover (hD : IsUnit (-16*(4*A^3+27*B^2))) : ⊤ ≤ iSup (opens A B) := by
  intro x _
  rcases InvariantChartCover318.charts_cover A B hD x with ⟨i,q,rfl⟩ | ⟨q,rfl⟩
  · fin_cases i
    · exact Opens.mem_iSup.mpr ⟨⟨.x⟩,⟨q,trivial,rfl⟩⟩
    · exact Opens.mem_iSup.mpr ⟨⟨.finite⟩,⟨q,trivial,rfl⟩⟩
  · exact Opens.mem_iSup.mpr ⟨⟨.infinity⟩,⟨q,trivial,rfl⟩⟩

theorem compatible (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    TopCat.Presheaf.IsCompatible (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf
      (opens A B) (localSection A B) := by
  rintro ⟨i⟩ ⟨j⟩
  cases i <;> cases j
  · rfl
  · exact WeierstrassIntrinsicOverlaps318.x_finite A B
  · exact WeierstrassIntrinsicOverlaps318.x_infinity A B hD
  · exact LocalSectionCompatibility318.symm _ _ _ _ _ (WeierstrassIntrinsicOverlaps318.x_finite A B)
  · rfl
  · exact WeierstrassIntrinsicOverlaps318.finite_infinity A B
  · exact LocalSectionCompatibility318.symm _ _ _ _ _ (WeierstrassIntrinsicOverlaps318.x_infinity A B hD)
  · exact LocalSectionCompatibility318.symm _ _ _ _ _ (WeierstrassIntrinsicOverlaps318.finite_infinity A B)
  · rfl

theorem local_free (i : ULift.{u} Chart)
    (V : (WeierstrassGluing318.scheme A B).Opens) (hV : V ≤ opens A B i) :
    Function.Bijective (fun a : Γ(WeierstrassGluing318.scheme A B,V) =>
      a • (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (homOfLE hV).op
        (localSection A B i)) := by
  rcases i with ⟨i⟩
  cases i
  · exact IntrinsicChartFrames318.generator_bijective _ _ (IntrinsicFamilyFrames318.finite_structure A B 0)
      (InvariantNormalizedFrames318.xFrame A B) _ (InvariantNormalizedFrames318.x_normalized A B) V hV
  · exact IntrinsicChartFrames318.generator_bijective _ _ (IntrinsicFamilyFrames318.finite_structure A B 1)
      (InvariantNormalizedFrames318.finiteFrame A B) _ (InvariantNormalizedFrames318.finite_normalized A B) V hV
  · exact IntrinsicChartFrames318.generator_bijective _ _ (IntrinsicFamilyFrames318.infinity_structure A B)
      (InvariantNormalizedFrames318.infinityFrame A B) _ (InvariantNormalizedFrames318.infinity_normalized A B) V hV

/-- The invariant differential is an actual global section of canonical Omega,
obtained by the sheaf gluing axiom from the three explicit chart forms. -/
@[expose] def invariant (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    Γ(FamilyIntrinsicDifferentials318.familyOmega A B,⊤) :=
  ModuleGlobalSections318.gluedTop _ (opens A B) (cover A B hD)
    (localSection A B) (compatible A B hD)

theorem invariant_restrict (hD : IsUnit (-16*(4*A^3+27*B^2))) (i : ULift.{u} Chart) :
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show opens A B i ≤ ⊤ from le_top)).op (invariant A B hD) = localSection A B i :=
  ModuleGlobalSections318.gluedTop_restrict _ (opens A B) (cover A B hD)
    (localSection A B) (compatible A B hD) i

/-- The actual canonical relative differential sheaf of the smooth completed
Weierstrass family has the globally glued invariant differential as a genuine
free generator. The three normalized chart forms agree on full intersections. -/
@[expose] def frame (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    FamilyIntrinsicDifferentials318.familyOmega A B ≅ GlobalInvariantLine318.line A B :=
  (ModuleFrameDescent318.gluedFrame (FamilyIntrinsicDifferentials318.familyOmega A B) (opens A B) (cover A B hD)
    (localSection A B) (compatible A B hD) (local_free A B)).symm

/-- The global frame retains the specified invariant generator on every chart. -/
theorem frame_inv_local (hD : IsUnit (-16*(4*A^3+27*B^2))) (i : ULift.{u} Chart)
    (a : Γ(WeierstrassGluing318.scheme A B,opens A B i)) :
    (frame A B hD).inv.val.app (op (opens A B i)) a = a • localSection A B i :=
  ModuleGlobalSections318.gluedMap_local _ (opens A B) (cover A B hD)
    (localSection A B) (compatible A B hD) i a
end IntrinsicGlobalFrame318
