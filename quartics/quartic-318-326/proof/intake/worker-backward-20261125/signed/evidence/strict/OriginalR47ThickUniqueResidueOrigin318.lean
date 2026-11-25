module
public import OriginalUpperR40SplitFieldFibre318
public section
noncomputable section

namespace OriginalR47ThickUniqueResidueOrigin318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalThickCentralReesChart318 (O I x y w oldToNew)
open OriginalLiteralThickNodeReesAtlas318 (central central_over)
open OriginalUpperR40PullbackChart318 (Pj localRead)
open OriginalUpperR40PullbackAffine318 (affineIso affineIso_read)
open OriginalUpperR40SplitFieldFibre318 (cf toOld baseRead)
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]

@[expose] def zeroPoint : Spec (CommRingCat.of (Node (0:k))) :=
  PrimeSpectrum.comap (eval (0:k) (0:k) 0 (by simp)).toRingHom (IsLocalRing.closedPoint k)

theorem zero_axes_iff (z : Spec (CommRingCat.of (Node (0:k)))) :
    (xAxis (0:k) ∈ z.asIdeal ∧ yAxis (0:k) ∈ z.asIdeal) ↔ z = zeroPoint k := by
  classical
  let ev := eval (0:k) (0:k) 0 (by simp)
  constructor
  · intro ⟨hx,hy⟩
    let Q := Ideal.Quotient.mkₐ k z.asIdeal
    have H : (Algebra.ofId k (Node (0:k) ⧸ z.asIdeal)).comp ev = Q := by
      apply OriginalNodeRingMaps318.ext
      · change algebraMap k _ (ev (xAxis (0:k))) = Q (xAxis (0:k))
        rw [show ev (xAxis (0:k)) = 0 from eval_x _ _ _ _,map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hx).symm
      · change algebraMap k _ (ev (yAxis (0:k))) = Q (yAxis (0:k))
        rw [show ev (yAxis (0:k)) = 0 from eval_y _ _ _ _,map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hy).symm
    apply PrimeSpectrum.ext
    ext t
    change t ∈ z.asIdeal ↔ ev t ∈ IsLocalRing.maximalIdeal k
    rw [IsLocalRing.maximalIdeal_eq_bot,Ideal.mem_bot,← Ideal.Quotient.eq_zero_iff_mem]
    change Q t = 0 ↔ ev t = 0
    rw [← DFunLike.congr_fun H t]
    change algebraMap k (Node (0:k) ⧸ z.asIdeal) (ev t) = 0 ↔ _
    exact map_eq_zero_iff _ (algebraMap k (Node (0:k) ⧸ z.asIdeal)).injective
  · rintro rfl
    constructor
    · change ev (xAxis (0:k)) ∈ IsLocalRing.maximalIdeal k
      rw [show ev (xAxis (0:k)) = 0 from eval_x _ _ _ _]
      exact Ideal.zero_mem _
    · change ev (yAxis (0:k)) ∈ IsLocalRing.maximalIdeal k
      rw [show ev (yAxis (0:k)) = 0 from eval_y _ _ _ _]
      exact Ideal.zero_mem _

theorem transported_zero_axes {c : k} (hc : c = 0) :
    ∃! z : Spec (CommRingCat.of (Node c)), xAxis c ∈ z.asIdeal ∧ yAxis c ∈ z.asIdeal := by
  subst c
  exact ⟨zeroPoint k, (zero_axes_iff k _).mpr rfl,
    fun z hz => (zero_axes_iff k z).mp hz⟩

variable {R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (q : R) (hq : Irreducible q) (d : ℕ) [Algebra R k]
variable (f : O q d →ₐ[R] k)
variable (hzero : algebraMap R k q = 0) (hx : f (x q d) = 0) (hy : f (y q d) = 0)

include hzero hx hy in
/-- The actual central chart of the genuine R40 exceptional fibre, at
one fixed residue field. Its original thin/thick arithmetic origin
has exactly ONE point there when the central output thickness is positive.
This is not a singleton statement about the whole exceptional fibre. -/
theorem unique_origin (hd : d ≠ 0) :
    ∃! z : Pj (toOld q d) (baseRead q d f) (cf q hq d),
      xAxis (q^d) ∈ ((localRead (toOld q d) (baseRead q d f) (cf q hq d)) z).asIdeal ∧
      yAxis (q^d) ∈ ((localRead (toOld q d) (baseRead q d f) (cf q hq d)) z).asIdeal := by
  let : Algebra (O q d) k := f.toRingHom.toAlgebra
  let : Algebra (O q d) (Node (q^d)) := (oldToNew q d).toRingHom.toAlgebra
  let S := OriginalUpperR40SplitCentralScalar318.withRead q d f hzero hx hy
  let t := S.val
  let e := affineIso (toOld q d) (cf q hq d) (central_over q d hq.ne_zero) t
  let b := OriginalUpperR40SplitCentralScalar318.cbar (k:=k) q d
  let g := OriginalUpperR40SplitCentralScalar318.scalarNode (k:=k) q d
  have he := affineIso_read (toOld q d) (cf q hq d) (central_over q d hq.ne_zero) t
  have hmap : (t.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R:=O q d) (A:=k) (B:=Node (q^d))).toRingHom) =
        g.toRingHom := by
    apply RingHom.ext
    intro z
    exact S.property z
  have hRead : e.hom ≫ localRead (toOld q d) (baseRead q d f) (cf q hq d) =
      Spec.map (CommRingCat.ofHom g.toRingHom) :=
    he.trans (congrArg (fun F : Node (q^d) →+* Node b => Spec.map (CommRingCat.ofHom F)) hmap)
  let P := fun z : Pj (toOld q d) (baseRead q d f) (cf q hq d) =>
    xAxis (q^d) ∈ ((localRead (toOld q d) (baseRead q d f) (cf q hq d)) z).asIdeal ∧
    yAxis (q^d) ∈ ((localRead (toOld q d) (baseRead q d f) (cf q hq d)) z).asIdeal
  have hIff (z : Spec (CommRingCat.of (Node b))) :
      P (e.hom z) ↔ xAxis b ∈ z.asIdeal ∧ yAxis b ∈ z.asIdeal := by
    change (_ ∈ _ ∧ _ ∈ _) ↔ _
    have hpoint := congrArg (fun F : Spec (CommRingCat.of (Node b)) ⟶
      Spec (CommRingCat.of (Node (q^d))) => F z) hRead
    rw [Scheme.Hom.comp_apply] at hpoint
    let t₀ : PrimeSpectrum (Node (q^d)) :=
      localRead (toOld q d) (baseRead q d f) (cf q hq d) (e.hom z)
    let z₀ : PrimeSpectrum (Node b) := z
    have ht₀ : t₀ = PrimeSpectrum.comap g.toRingHom z₀ := hpoint
    change (xAxis (q^d) ∈ t₀.asIdeal ∧ yAxis (q^d) ∈ t₀.asIdeal) ↔
      (xAxis b ∈ z₀.asIdeal ∧ yAxis b ∈ z₀.asIdeal)
    rw [ht₀]
    change (g (xAxis (q^d)) ∈ z₀.asIdeal ∧ g (yAxis (q^d)) ∈ z₀.asIdeal) ↔ _
    rw [show g (xAxis (q^d)) = xAxis b from eval_x _ _ _ _,
      show g (yAxis (q^d)) = yAxis b from eval_y _ _ _ _]
  have hb : b = 0 := (OriginalUpperR40SplitCentralScalar318.cbar_eq q d hzero).trans (ite_eq_right hd)
  obtain ⟨z,hz,hunique⟩ := transported_zero_axes k hb
  refine ⟨e.hom z, (hIff z).mpr hz,?_⟩
  intro w hw
  obtain ⟨v,rfl⟩ := (Scheme.homeoOfIso e).surjective w
  exact congrArg e.hom (hunique v ((hIff v).mp hw))

end OriginalR47ThickUniqueResidueOrigin318

#print axioms OriginalR47ThickUniqueResidueOrigin318.zero_axes_iff
#print axioms OriginalR47ThickUniqueResidueOrigin318.unique_origin
