module
public import OriginalR47OriginalReesOverlaps318
public import Mathlib.AlgebraicGeometry.Cover.Directed
public section
noncomputable section

namespace OriginalR47IsolatedCentreCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : Scheme.{u}} (Z : Set X) (hZ : Z.Finite)
variable (hClosed : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z)

instance coverOrder : Preorder (oldCover Z hZ hClosed pick).I₀ :=
  inferInstanceAs (Preorder (Idx Z hZ hClosed pick))

@[expose] def trans {i j : Idx Z hZ hClosed pick} (h : i ⟶ j) :
    (oldCover Z hZ hClosed pick).X i ⟶ (oldCover Z hZ hClosed pick).X j :=
  OriginalR47GlobalCentreRees318.oldStep Z hZ hClosed pick h

@[reassoc (attr := simp)]
theorem trans_read {i j : Idx Z hZ hClosed pick} (h : i ⟶ j) :
    trans Z hZ hClosed pick h ≫ (oldCover Z hZ hClosed pick).f j =
      (oldCover Z hZ hClosed pick).f i :=
  OriginalR47GlobalCentreRees318.oldStep_over Z hZ hClosed pick h

instance coverDirected : (oldCover Z hZ hClosed pick).LocallyDirected where
  trans {i j} hij := trans Z hZ hClosed pick (i:=i) (j:=j) hij
  trans_id := OriginalR47GlobalCentreRees318.oldStep_id Z hZ hClosed pick
  trans_comp {i j k} hij hjk :=
    OriginalR47GlobalCentreRees318.oldStep_comp Z hZ hClosed pick (i:=i) (j:=j) (k:=k) hij hjk
  w {i j} hij := trans_read Z hZ hClosed pick (i:=i) (j:=j) hij
  directed {i j} x := by
    let C := oldCover Z hZ hClosed pick
    let m := pullback.fst (C.f i) (C.f j) ≫ C.f i
    let : IsOpenImmersion (C.f i) := C.map_prop i
    let : IsOpenImmersion (C.f j) := C.map_prop j
    let : IsOpenImmersion m := inferInstance
    let ii : Idx Z hZ hClosed pick := i
    let jj : Idx Z hZ hClosed pick := j
    let Ui : X.Opens := idxOpen Z hZ hClosed pick ii
    let Uj : X.Opens := idxOpen Z hZ hClosed pick jj
    let xi : Ui.toScheme := pullback.fst (C.f i) (C.f j) x
    let xj : Uj.toScheme := pullback.snd (C.f i) (C.f j) x
    have hi' : Ui.ι xi = m x := (Scheme.Hom.comp_apply (pullback.fst (C.f i) (C.f j)) (C.f i) x).symm
    have hj' : Uj.ι xj = m x := by
      calc
        _ = (pullback.snd (C.f i) (C.f j) ≫ C.f j) x :=
          (Scheme.Hom.comp_apply (pullback.snd (C.f i) (C.f j)) (C.f j) x).symm
        _ = m x := congrArg (fun f : pullback (C.f i) (C.f j) ⟶ X => f x)
          (pullback.condition (f:=C.f i) (g:=C.f j)).symm
    have hi : m x ∈ Ui := hi' ▸ (show Ui.ι xi ∈ Ui from xi.property)
    have hj : m x ∈ Uj := hj' ▸ (show Uj.ι xj ∈ Uj from xj.property)
    obtain ⟨k,hki,hkj,hcap⟩ := common_below Z hZ hClosed pick ii jj
    let y : (idxOpen Z hZ hClosed pick k).toScheme := ⟨m x,hcap ⟨hi,hj⟩⟩
    have hy : C.f k y = m x := Scheme.Opens.ι_apply _ y
    refine ⟨k,homOfLE hki,homOfLE hkj,y,?_⟩
    apply m.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply]
    change (pullback.lift (trans Z hZ hClosed pick (homOfLE hki))
      (trans Z hZ hClosed pick (homOfLE hkj)) _ ≫
        (pullback.fst (C.f i) (C.f j) ≫ C.f i)) y = m x
    rw [pullback.lift_fst_assoc,trans_read]
    exact hy
  property_trans {i j} hij := by
    change IsOpenImmersion (X.homOfLE
      (show idxOpen Z hZ hClosed pick i ≤ idxOpen Z hZ hClosed pick j from leOfHom hij))
    infer_instance

end OriginalR47IsolatedCentreCover318

#print axioms OriginalR47IsolatedCentreCover318.coverDirected
