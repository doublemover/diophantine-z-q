module
public import SelectedPointedShortScaling318
public import SelectedSecantAdditionScaling318
public import SelectedCompletedSecant318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318

namespace SelectedCompletedAdditiveScaling318
open SelectedPointedShortScaling318
variable {R : Type u} [CommRing R]
variable (A B C D : R) (r : Rˣ)
variable (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)
local notation "γ" => gluedMap A B C D r hA hB
local notation "φ" => SelectedPointedShortScaling318.finiteMap A B C D r hA hB
local notation "σ" => SelectedSecantAdditionScaling318.secantMap A B C D r hA hB
local notation "i" => SelectedCompletedSecant318.intoPair

/-- Actual map on the completed relative square induced by the previously
constructed pointed map on the literal short cubes. -/
@[expose] def pairMap :
    pullback (structureMap C D) (structureMap C D) ⟶
      pullback (structureMap A B) (structureMap A B) :=
  pullback.lift (pullback.fst _ _ ≫ γ) (pullback.snd _ _ ≫ γ) (by
    simpa only [Category.assoc,glued_base] using
      (pullback.condition (f := structureMap C D) (g := structureMap C D)))

local notation "P" => pairMap A B C D r hA hB

@[reassoc] theorem pair_fst : P ≫ pullback.fst _ _ = pullback.fst _ _ ≫ γ := by simp [pairMap]
@[reassoc] theorem pair_snd : P ≫ pullback.snd _ _ = pullback.snd _ _ ≫ γ := by simp [pairMap]

private abbrev leftProjection (X Y : R) :=
  Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.left X Y).toRingHom)
private abbrev rightProjection (X Y : R) :=
  Spec.map (CommRingCat.ofHom (RelativeChordAlgebra318.right X Y).toRingHom)

private theorem secant_left : σ ≫ leftProjection A B = leftProjection C D ≫ φ := by
  unfold SelectedSecantAdditionScaling318.secantMap SelectedPointedShortScaling318.finiteMap
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (SelectedSecantAdditionScaling318.left_projection A B C D r hA hB))

private theorem secant_right : σ ≫ rightProjection A B = rightProjection C D ≫ φ := by
  unfold SelectedSecantAdditionScaling318.secantMap SelectedPointedShortScaling318.finiteMap
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (SelectedSecantAdditionScaling318.right_projection A B C D r hA hB))

private theorem intoPair_fst (X Y : R) :
    i X Y ≫ pullback.fst _ _ = leftProjection X Y ≫ finiteChart X Y := by
  rw [SelectedCompletedSecant318.intoPair,Category.assoc,
    FiniteProductSchematicDensity318.pairMap_fst,←Category.assoc,RelativeChordScheme318.intoProduct_fst]

private theorem intoPair_snd (X Y : R) :
    i X Y ≫ pullback.snd _ _ = rightProjection X Y ≫ finiteChart X Y := by
  rw [SelectedCompletedSecant318.intoPair,Category.assoc,
    FiniteProductSchematicDensity318.pairMap_snd,←Category.assoc,RelativeChordScheme318.intoProduct_snd]

/-- Lower-left map on the chosen actual secant open is the restriction
of the true completed square map, on both projections. -/
theorem pair_on_secant : i C D ≫ P = σ ≫ i A B := by
  apply pullback.hom_ext
  · calc
      _ = leftProjection C D ≫ (φ ≫ finiteChart A B) := by
        rw [Category.assoc,pair_fst,←Category.assoc,intoPair_fst,Category.assoc,finite_glued]
      _ = (σ ≫ i A B) ≫ pullback.fst _ _ := by
        symm
        rw [Category.assoc,intoPair_fst,←Category.assoc,secant_left,Category.assoc]
  · calc
      _ = rightProjection C D ≫ (φ ≫ finiteChart A B) := by
        rw [Category.assoc,pair_snd,←Category.assoc,intoPair_snd,Category.assoc,finite_glued]
      _ = (σ ≫ i A B) ≫ pullback.snd _ _ := by
        symm
        rw [Category.assoc,intoPair_snd,←Category.assoc,secant_right,Category.assoc]

include hA hB in
theorem discriminant_scale :
    -16*(4*A^3+27*B^2) = (r:R)^12*(-16*(4*C^3+27*D^2)) := by
  rw [hA,hB]
  ring

include hA hB in
theorem target_smooth_disc (h : IsUnit (-16*(4*C^3+27*D^2))) :
    IsUnit (-16*(4*A^3+27*B^2)) := by
  rw [discriminant_scale A B C D r hA hB]
  exact (r.isUnit.pow 12).mul h

/-- The actual completed addition square commutes, by schematic rather
than set-theoretic density. This holds over an arbitrary commutative ring
where the old discriminant is a unit. -/
theorem addition (h : IsUnit (-16*(4*C^3+27*D^2))) :
    P ≫ CompletedAddition318.addition A B (target_smooth_disc A B C D r hA hB h) =
      CompletedAddition318.addition C D h ≫ γ := by
  let ha := target_smooth_disc A B C D r hA hB h
  apply SelectedCompletedSecant318.maps_ext C D A B h
  · simp only [Category.assoc,CompletedAddition318.addition_over_base,pair_fst_assoc,glued_base]
  · calc
      _ = (σ ≫ i A B) ≫ CompletedAddition318.addition A B ha := by
        rw [←Category.assoc,pair_on_secant]
      _ = σ ≫ (RelativeChordScheme318.addition A B ≫ finiteChart A B) := by
        rw [Category.assoc,SelectedCompletedSecant318.completed_addition_restrict]
      _ = RelativeChordScheme318.addition C D ≫ (φ ≫ finiteChart A B) := by
        rw [←Category.assoc,SelectedSecantAdditionScaling318.secant_addition,Category.assoc] <;> rfl
      _ = i C D ≫ (CompletedAddition318.addition C D h ≫ γ) := by
        symm
        rw [←Category.assoc,SelectedCompletedSecant318.completed_addition_restrict,
          Category.assoc,finite_glued]

end SelectedCompletedAdditiveScaling318

#print axioms SelectedCompletedAdditiveScaling318.pair_on_secant
#print axioms SelectedCompletedAdditiveScaling318.addition
