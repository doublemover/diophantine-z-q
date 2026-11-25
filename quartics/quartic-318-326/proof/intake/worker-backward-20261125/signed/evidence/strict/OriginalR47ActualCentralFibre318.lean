module
public import OriginalR47ThickUniqueResidueOrigin318
public import OriginalR47LiteralNodeCentre318
public import Mathlib.AlgebraicGeometry.Fiber
public section
noncomputable section

namespace OriginalR47ActualCentralFibre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalSplitNodeCoordinates318
open OriginalAffineReesBlowup318
open OriginalThickCentralReesChart318 (O I x y w hw)
open OriginalUpperR40SplitFieldFibre318 (toOld baseRead cf)
open OriginalUpperR40PullbackChart318 (Pj localRead)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] [IsDomain R]
variable (q : R) (hq : Irreducible q) (d : ℕ)
local notation "N" => Spec (CommRingCat.of (Node (q^d)))
local notation "S" => Spec (CommRingCat.of (O q d))

/-- The two-axis condition is intrinsic to the literal central R40 chart. -/
abbrev atAxes (z : N) : Prop :=
  xAxis (q^d) ∈ z.asIdeal ∧ yAxis (q^d) ∈ z.asIdeal

section GeometricReading
variable [UniqueFactorizationMonoid R]
local notation "j" => cf q hq d

/-- Exact selected field read: no separate coefficient homomorphism
or coordinate-vanishing hypothesis is supplied. -/
theorem over_field {k : Type} [Field k]
    (r : Spec (CommRingCat.of k) ⟶ S)
    (hr : ∀ t, (r t).asIdeal = I q d) (hd : d ≠ 0) :
    ∃! z : Pj (toOld q d) r j, atAxes q d (localRead (toOld q d) r j z) := by
  obtain ⟨g,hg⟩ := Spec.map_surjective r
  let : Algebra R k := (g.hom.comp (algebraMap R (O q d))).toAlgebra
  let f : O q d →ₐ[R] k := ⟨g.hom, fun _ => rfl⟩
  have hf : baseRead q d f = r := hg
  have hker (u : O q d) (hu : u ∈ I q d) : f u = 0 := by
    have hp := hr (IsLocalRing.closedPoint k)
    rw [← hf] at hp
    have hu' : u ∈ (baseRead q d f (IsLocalRing.closedPoint k)).asIdeal := by
      rwa [hp]
    change f u ∈ IsLocalRing.maximalIdeal k at hu'
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hu'
  have hzero : algebraMap R k q = 0 :=
    (f.commutes q).symm.trans (hker (w q d) (hw q d))
  rw [← hf]
  exact OriginalR47ThickUniqueResidueOrigin318.unique_origin k q hq d f hzero
    (hker (x q d) (Ideal.subset_span (by simp)))
    (hker (y q d) (Ideal.subset_span (by simp))) hd

/-- The same unique origin in the exact central pullback chart, on the
point fibre over t. This is not a statement about the whole exceptional
curve, and t need not be rational over the old centre field. -/
theorem in_cartesian_chart {T V : Scheme}
    (l : V ⟶ N) (p : V ⟶ T) (b : T ⟶ S)
    (H : IsPullback l p (j ≫ toOld q d) b)
    (t : T) (hcentre : (b t).asIdeal = I q d) (hd : d ≠ 0) :
    ∃! v : V, p v = t ∧ atAxes q d (l v) := by
  let r := T.fromSpecResidueField t ≫ b
  have hr (a : Spec (T.residueField t)) : (r a).asIdeal = I q d := by
    rw [show r a = b t by
      exact (Scheme.Hom.comp_apply (T.fromSpecResidueField t) b a).trans
        (congrArg (fun y : T => b y) (T.fromSpecResidueField_apply t a))]
    exact hcentre
  let U := Pj (toOld q d) r j
  let L : IsPullback (p.fiberToSpecResidueField t) (p.fiberι t ≫ l)
      r (j ≫ toOld q d) :=
    ((IsPullback.of_hasPullback p (T.fromSpecResidueField t)).paste_horiz H).flip
  let e : p.fiber t ≅ U := L.isoPullback
  have hm : e.hom ≫ localRead (toOld q d) r j = p.fiberι t ≫ l :=
    L.isoPullback_hom_snd
  have hl (a : p.fiber t) :
      localRead (toOld q d) r j (e.hom a) = l (p.fiberι t a) := by
    exact (Scheme.Hom.comp_apply e.hom (localRead (toOld q d) r j) a).symm.trans
      ((congrArg (fun h : p.fiber t ⟶ N => h a) hm).trans
        (Scheme.Hom.comp_apply (p.fiberι t) l a))
  obtain ⟨z,hz,huniq⟩ := over_field q hq d r hr hd
  let u := e.inv z
  have he : e.hom u = z := by
    change e.hom (e.inv z) = z
    exact (Scheme.homeoOfIso e).apply_symm_apply z
  have hv : p (p.fiberι t u) = t := by
    have ht : p.fiberι t u ∈ Set.range (p.fiberι t) := ⟨u,rfl⟩
    rw [p.range_fiberι] at ht
    exact ht
  refine ⟨p.fiberι t u, ⟨hv,?_⟩,?_⟩
  · rwa [← hl u,he]
  · intro v hv
    have ht : v ∈ Set.range (p.fiberι t) := by
      rw [p.range_fiberι]
      exact hv.1
    obtain ⟨a,rfl⟩ := ht
    have ha := hv.2
    rw [← hl a] at ha
    have eha : e.hom a = e.hom u := (huniq _ ha).trans he.symm
    exact congrArg (p.fiberι t) ((Scheme.homeoOfIso e).injective eha)


end GeometricReading

section TrueTrait

variable [IsDiscreteValuationRing R]

include hq in
/-- The axes of the actual next q^(e+2) node force its full literal
centre ideal. The coefficient q is paid by primality and the true
old equation, and maximality is the checked R40 DVR ideal. -/
theorem axes_centre (e : ℕ) (t : PrimeSpectrum (O q e)) :
    atAxes q (e+2) t ↔ t.asIdeal = I q e := by
  constructor
  · intro h
    have hw0 : w q e ∈ t.asIdeal := by
      apply t.isPrime.mem_of_pow_mem (e+2)
      have hm : (w q e)^(e+2) = y q e * x q e := by
        change (algebraMap R (O q e) q)^(e+2) =
          yAxis (q^(e+2)) * xAxis (q^(e+2))
        rw [OriginalNodeRingMaps318.node_relation,map_pow]
      rw [hm]
      exact t.asIdeal.mul_mem_left _ h.1
    have hI : I q e ≤ t.asIdeal := Ideal.span_le.mpr (by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact h.1
      · exact h.2
      · exact hw0)
    exact ((OriginalR47LiteralNodeCentre318.maximal_of_dvr q e hq).eq_of_le
      t.isPrime.ne_top hI).symm
  · intro h
    have hx : x q e ∈ I q e := Ideal.subset_span (by simp)
    have hy : y q e ∈ I q e := Ideal.subset_span (by simp)
    change x q e ∈ t.asIdeal ∧ y q e ∈ t.asIdeal
    rw [h]
    exact ⟨hx,hy⟩

/-- Exact thick child, parameterized by its new offset e. The
*actual* central affine chart for old offset e+2 has thickness e+2;
it contributes exactly one point over the selected old residue point,
whose literal split chart is the input chart of the next Rees round.
No new degree or model is selected.

In particular the equation e + 2 = (old offset) is built into the
actual coordinate map, not inferred just from a rank or count. -/
theorem exact_child (e : ℕ) {T V : Scheme}
    (l : V ⟶ Spec (CommRingCat.of (O q e))) (p : V ⟶ T)
    (b : T ⟶ Spec (CommRingCat.of (O q (e+2))))
    (H : IsPullback l p ((cf q hq (e+2)) ≫ toOld q (e+2)) b)
    (t : T) (hcentre : (b t).asIdeal = I q (e+2)) :
    ∃! v : V, p v = t ∧ (l v).asIdeal = I q e := by
  obtain ⟨v,hv,huniq⟩ := in_cartesian_chart q hq (e+2) l p b H t hcentre (by omega)
  refine ⟨v,⟨hv.1,(axes_centre q hq e (l v)).mp hv.2⟩,?_⟩
  intro u hu
  exact huniq u ⟨hu.1,(axes_centre q hq e (l u)).mpr hu.2⟩

end TrueTrait

end OriginalR47ActualCentralFibre318

#print axioms OriginalR47ActualCentralFibre318.over_field
#print axioms OriginalR47ActualCentralFibre318.in_cartesian_chart
#print axioms OriginalR47ActualCentralFibre318.axes_centre
#print axioms OriginalR47ActualCentralFibre318.exact_child
