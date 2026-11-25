module
public import OriginalR47RelativeNodeDatum318
public section
noncomputable section

namespace OriginalR47FiniteEtaleSplitWindowBridge318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalR47RelativeNodeDatum318 OriginalR47RelativePointedWindow318
open OriginalSplitNodeCoordinates318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type} [CommRing T] {X : Scheme}
local notation "S" => Spec (CommRingCat.of T)
variable (f : X ⟶ S) (x : X) (P : Parameters T)
local notation "h" => Spec.map (CommRingCat.ofHom P.φ)
local notation "fD" => pullback.snd f h
local notation "up" => pullback.fst f h

/-- The étale chart obtained after splitting the actual old fibre node
still has a genuinely finite-type étale map back to the original
arithmetic trait. This uses a finite étale coefficient ring, not a
stalk localization incorrectly claimed to be of finite type. The
literal D-equation has already been obtained on the two algebraic
étale neighbourhoods; a formal isomorphism alone is not a Window. -/
theorem descend (hflat : P.φ.Flat) (hfinite : P.φ.FiniteType)
    (t : pullback f h) (ht : up t = x) (δ : P.D)
    (W : Window fD t (Spec.algebraMap P.D (Node δ))) :
    ∃ J : Window f x (nodeBase P δ), J.g J.w = W.g W.w := by
  letI : Algebra T P.D := P.φ.toAlgebra
  letI : Algebra.FormallyEtale T P.D := P.formal
  have hUnram : P.φ.FormallyUnramified := by
    change (algebraMap T P.D).FormallyUnramified
    exact RingHom.formallyUnramified_algebraMap.mpr inferInstance
  letI : Flat h := Flat.SpecMap_iff.mpr hflat
  letI : FormallyUnramified h := (HasRingHomProperty.Spec_iff (P:=@FormallyUnramified)).mpr hUnram
  letI : LocallyOfFiniteType h := (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mpr hfinite
  letI : Flat up := MorphismProperty.pullback_fst f h (inferInstance : Flat h)
  letI : FormallyUnramified up := MorphismProperty.pullback_fst f h (inferInstance : FormallyUnramified h)
  letI : LocallyOfFiniteType up :=
    MorphismProperty.pullback_fst f h (inferInstance : LocallyOfFiniteType h)
  have hover : (W.e ≫ up) ≫ f = W.g ≫ nodeBase P δ := by
    calc
      _ = W.e ≫ up ≫ f := Category.assoc _ _ _
      _ = W.e ≫ fD ≫ h := congrArg (fun g => W.e ≫ g) pullback.condition
      _ = (W.e ≫ fD) ≫ h := (Category.assoc _ _ _).symm
      _ = (W.g ≫ Spec.algebraMap P.D (Node δ)) ≫ h :=
        congrArg (fun g => g ≫ h) W.over
      _ = _ := Category.assoc _ _ _
  let J : Window f x (nodeBase P δ) := {
    U := W.U
    w := W.w
    e := W.e ≫ up
    g := W.g
    eFlat := inferInstance
    eUnram := MorphismProperty.comp_mem (@FormallyUnramified) W.e up W.eUnram inferInstance
    eFinite := inferInstance
    gFlat := W.gFlat
    gUnram := W.gUnram
    gFinite := W.gFinite
    point := by rw [Scheme.Hom.comp_apply,W.point,ht]
    over := hover
  }
  exact ⟨J,rfl⟩

end OriginalR47FiniteEtaleSplitWindowBridge318

#print axioms OriginalR47FiniteEtaleSplitWindowBridge318.descend
