module
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public section
noncomputable section

namespace OriginalR47PointedSiteActualAffine318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {U X : Scheme.{u}} {A C : CommRingCat.{u}}
variable (e : U ⟶ X) (l : U ⟶ Spec C) (j : Spec A ⟶ X)
variable (u₀ : U) (p : Spec A)

structure Chart where
  B : CommRingCat.{u}
  inc : Spec B ⟶ U
  [openInc : IsOpenImmersion inc]
  old : A ⟶ B
  split : C ⟶ B
  point : Spec B
  point_read : inc point = u₀
  old_read : Spec.map old point = p
  split_read : Spec.map split point = l u₀
  old_comm : Spec.map old ≫ j = inc ≫ e
  split_comm : Spec.map split = inc ≫ l
  old_flat : old.hom.Flat
  split_flat : split.hom.Flat
  old_unram : old.hom.FormallyUnramified
  split_unram : split.hom.FormallyUnramified
  old_finite : old.hom.FiniteType
  split_finite : split.hom.FiniteType

attribute [instance] Chart.openInc

/-- Choose the actual common affine chart in U×_X Spec A at the marked
preimage of u₀ and p. Both ring maps are literally Spec.preimage of the
two composited scheme maps; their equality to the arrows is derived. -/
theorem choose [IsOpenImmersion j]
    [Flat e] [FormallyUnramified e] [LocallyOfFiniteType e]
    [Flat l] [FormallyUnramified l] [LocallyOfFiniteType l]
    (hp : e u₀ = j p) : Nonempty (Chart e l j u₀ p) := by
  let T := pullback e j
  obtain ⟨t,ht,ht'⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback e j) u₀ p hp
  let W := T.affineOpenCover
  obtain ⟨i,v,hv⟩ := W.openCover.exists_eq t
  let B := W.X i
  let k : Spec B ⟶ T := W.f i
  let inc : Spec B ⟶ U := k ≫ pullback.fst e j
  let oldSpec : Spec B ⟶ Spec A := k ≫ pullback.snd e j
  let splitSpec : Spec B ⟶ Spec C := inc ≫ l
  let φ : A ⟶ B := Spec.preimage oldSpec
  let ψ : C ⟶ B := Spec.preimage splitSpec
  have old_map : Spec.map φ = oldSpec := Spec.map_preimage _
  have split_map : Spec.map ψ = splitSpec := Spec.map_preimage _
  have hi : inc v = u₀ := by
    change (k ≫ pullback.fst e j) v = u₀
    rw [Scheme.Hom.comp_apply]
    exact (congrArg (pullback.fst e j) hv).trans ht
  have ho : Spec.map φ v = p := by
    rw [old_map]
    change (k ≫ pullback.snd e j) v = p
    rw [Scheme.Hom.comp_apply]
    exact (congrArg (pullback.snd e j) hv).trans ht'
  have hComm : Spec.map φ ≫ j = inc ≫ e := by
    rw [old_map]
    change (k ≫ pullback.snd e j) ≫ j = (k ≫ pullback.fst e j) ≫ e
    rw [Category.assoc,Category.assoc,pullback.condition]
  let : IsOpenImmersion (pullback.fst e j) := inferInstance
  let : IsOpenImmersion k := W.map_prop i
  let : IsOpenImmersion inc := inferInstanceAs (IsOpenImmersion (k ≫ pullback.fst e j))
  let : Flat oldSpec := inferInstanceAs (Flat (k ≫ pullback.snd e j))
  let : Flat splitSpec := inferInstanceAs (Flat (inc ≫ l))
  let : LocallyOfFiniteType oldSpec := inferInstanceAs (LocallyOfFiniteType (k ≫ pullback.snd e j))
  let : LocallyOfFiniteType splitSpec := inferInstanceAs (LocallyOfFiniteType (inc ≫ l))
  have hOldUnram : FormallyUnramified oldSpec :=
    MorphismProperty.comp_mem (@FormallyUnramified) k (pullback.snd e j) inferInstance
      (MorphismProperty.pullback_snd (P:=@FormallyUnramified) e j inferInstance)
  have hSplitUnram : FormallyUnramified splitSpec :=
    MorphismProperty.comp_mem (@FormallyUnramified) inc l inferInstance inferInstance
  refine ⟨{
    B := B
    inc := inc
    openInc := inferInstance
    old := φ
    split := ψ
    point := v
    point_read := hi
    old_read := ho
    split_read := ?_
    old_comm := hComm
    split_comm := split_map
    old_flat := ?_
    split_flat := ?_
    old_unram := ?_
    split_unram := ?_
    old_finite := ?_
    split_finite := ?_
  }⟩
  · rw [split_map]
    exact (Scheme.Hom.comp_apply inc l v).trans (congrArg l hi)
  · exact Flat.SpecMap_iff.mp (old_map.symm ▸ (inferInstance : Flat oldSpec))
  · exact Flat.SpecMap_iff.mp (split_map.symm ▸ (inferInstance : Flat splitSpec))
  · exact (HasRingHomProperty.Spec_iff (P:=@FormallyUnramified)).mp
      (old_map.symm ▸ hOldUnram)
  · exact (HasRingHomProperty.Spec_iff (P:=@FormallyUnramified)).mp
      (split_map.symm ▸ hSplitUnram)
  · exact (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp
      (old_map.symm ▸ (inferInstance : LocallyOfFiniteType oldSpec))
  · exact (HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)).mp
      (split_map.symm ▸ (inferInstance : LocallyOfFiniteType splitSpec))

end OriginalR47PointedSiteActualAffine318

#print axioms OriginalR47PointedSiteActualAffine318.choose
