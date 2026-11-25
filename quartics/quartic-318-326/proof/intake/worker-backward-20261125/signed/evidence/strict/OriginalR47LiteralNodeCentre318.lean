module
public import OriginalR40ActualOldChartMaps318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public section
noncomputable section

namespace OriginalR47LiteralNodeCentre318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalThickCentralReesChart318 (O x y w I)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type*} [CommRing R] (q : R) (d : ℕ)

abbrev uniformizerIdeal : Ideal R := Ideal.span ({q} : Set R)
abbrev residue := R ⧸ uniformizerIdeal q

theorem q_zero : algebraMap R (residue q) q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton q))

/-- Evaluation on the actual split node of thickness d+2; both axes
are zero, and coefficients are reduced mod the actual uniformizer. -/
@[expose] def toResidue : O q d →ₐ[R] residue q :=
  eval (q^(d+2)) 0 0 (by
    rw [zero_mul, map_pow, q_zero q, zero_pow (by omega : d+2 ≠ 0)])

theorem killCentre : I q d ≤ RingHom.ker (toResidue q d).toRingHom := by
  apply Ideal.span_le.mpr
  intro z hz
  change toResidue q d z = 0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with (rfl | rfl | rfl)
  · exact eval_x _ _ _ _
  · exact eval_y _ _ _ _
  · exact (toResidue q d).commutes q |>.trans (q_zero q)

@[expose] def quotientToResidue : (O q d ⧸ I q d) →ₐ[R] residue q :=
  Ideal.Quotient.liftₐ _ (toResidue q d) (fun _ h => killCentre q d h)

theorem uniformizer_killed :
    uniformizerIdeal q ≤ RingHom.ker (algebraMap R (O q d ⧸ I q d)) := by
  apply Ideal.span_le.mpr
  intro z hz
  have h : z = q := Set.mem_singleton_iff.mp hz
  subst z
  change Ideal.Quotient.mk (I q d) (w q d) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (OriginalThickCentralReesChart318.hw q d)

@[expose] def residueToQuotient : residue q →ₐ[R] (O q d ⧸ I q d) :=
  Ideal.Quotient.liftₐ _ (Algebra.ofId R (O q d ⧸ I q d))
    (fun _ h => uniformizer_killed q d h)

theorem inverse_on_node :
    (residueToQuotient q d).comp
      ((quotientToResidue q d).comp (Ideal.Quotient.mkₐ R (I q d))) =
      Ideal.Quotient.mkₐ R (I q d) := by
  rw [quotientToResidue, Ideal.Quotient.liftₐ_comp]
  apply OriginalNodeRingMaps318.ext
  · change residueToQuotient q d (toResidue q d (x q d)) = Ideal.Quotient.mk (I q d) (x q d)
    rw [show toResidue q d (x q d) = 0 from eval_x _ _ _ _,
      map_zero (residueToQuotient q d)]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
  · change residueToQuotient q d (toResidue q d (y q d)) = Ideal.Quotient.mk (I q d) (y q d)
    rw [show toResidue q d (y q d) = 0 from eval_y _ _ _ _,
      map_zero (residueToQuotient q d)]
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm

theorem kernel_eq :
    RingHom.ker (toResidue q d).toRingHom = I q d := by
  apply le_antisymm _ (killCentre q d)
  intro z hz
  change toResidue q d z = 0 at hz
  have H := DFunLike.congr_fun (inverse_on_node q d) z
  change residueToQuotient q d (toResidue q d z) = Ideal.Quotient.mk (I q d) z at H
  rw [hz, map_zero (residueToQuotient q d)] at H
  exact (Ideal.Quotient.eq_zero_iff_mem).mp H.symm

/-- The literal R40 centre is the closed point once q generates the
maximal ideal of the actual trait, not merely when q is irreducible in a UFD. -/
theorem maximal [ (uniformizerIdeal q).IsMaximal ] : (I q d).IsMaximal := by
  let : Field (residue q) := Ideal.Quotient.field (uniformizerIdeal q)
  rw [← kernel_eq q d]
  apply RingHom.ker_isMaximal_of_surjective
  intro z
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨algebraMap R (O q d) r, (toResidue q d).commutes r⟩

/-- The original R47 trait hands us a DVR and an irreducible q; no
separate maximality assumption at its literal node remains. -/
theorem uniformizer_maximal [IsDomain R] [IsDiscreteValuationRing R] (hq : Irreducible q) :
    (uniformizerIdeal q).IsMaximal := by
  change (Ideal.span ({q} : Set R)).IsMaximal
  rw [← hq.maximalIdeal_eq]
  exact IsLocalRing.maximalIdeal.isMaximal R

theorem maximal_of_dvr [IsDomain R] [IsDiscreteValuationRing R] (hq : Irreducible q) :
    (I q d).IsMaximal := by
  let : (uniformizerIdeal q).IsMaximal := uniformizer_maximal q hq
  exact maximal q d

end OriginalR47LiteralNodeCentre318

#print axioms OriginalR47LiteralNodeCentre318.kernel_eq
#print axioms OriginalR47LiteralNodeCentre318.maximal
#print axioms OriginalR47LiteralNodeCentre318.maximal_of_dvr
