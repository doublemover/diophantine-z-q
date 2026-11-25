module
public import OriginalR47LiteralNodeCentre318
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public section
noncomputable section

namespace OriginalR47LiteralDoubleOrigin318

open OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
open OriginalR47LiteralNodeCentre318 (uniformizerIdeal residue q_zero uniformizer_maximal)
open AlgebraicGeometry Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R] (q : R) (m : ℕ)

/-- Actual residual value on the two named axes of the literal
node, including thickness one. -/
@[expose] def atOrigin (hm : m ≠ 0) : Node (q^m) →ₐ[R] residue q :=
  eval (q^m) 0 0 (by rw [zero_mul,map_pow,q_zero q,zero_pow hm])

theorem q_mem (z : PrimeSpectrum (Node (q^m))) (hx : xAxis (q^m) ∈ z.asIdeal)
    (hy : yAxis (q^m) ∈ z.asIdeal) : algebraMap R (Node (q^m)) q ∈ z.asIdeal := by
  apply z.isPrime.mem_of_pow_mem m
  rw [← map_pow,← node_relation]
  exact z.asIdeal.mul_mem_left _ hx

/-- The actual point with two nonunit axes on a node of positive
thickness is precisely the kernel of old coefficient reduction.
This uses the full original ring with its uniformizer, not a
component guessed from the abstract residue curve. -/
theorem kernel (hm : m ≠ 0) [(uniformizerIdeal q).IsMaximal]
    (z : PrimeSpectrum (Node (q^m))) (hx : xAxis (q^m) ∈ z.asIdeal)
    (hy : yAxis (q^m) ∈ z.asIdeal) :
    RingHom.ker (atOrigin q m hm).toRingHom = z.asIdeal := by
  letI : Field (residue q) := Ideal.Quotient.field (uniformizerIdeal q)
  let T := Node (q^m) ⧸ z.asIdeal
  let a : Node (q^m) →ₐ[R] T := Ideal.Quotient.mkₐ R z.asIdeal
  let b : R →ₐ[R] T := Algebra.ofId R T
  have hq : uniformizerIdeal q ≤ RingHom.ker b.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx'
    have he : x = q := Set.mem_singleton_iff.mp hx'
    subst x
    change Ideal.Quotient.mk z.asIdeal (algebraMap R (Node (q^m)) q) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (q_mem q m z hx hy)
  let τ : residue q →ₐ[R] T :=
    Ideal.Quotient.liftₐ _ b (fun _ h => hq h)
  have hcomp : τ.comp (atOrigin q m hm) = a := by
    apply OriginalNodeRingMaps318.ext
    · change τ (atOrigin q m hm (xAxis (q^m))) = Ideal.Quotient.mk z.asIdeal (xAxis (q^m))
      rw [show atOrigin q m hm (xAxis (q^m)) = 0 from eval_x _ _ _ _,map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hx).symm
    · change τ (atOrigin q m hm (yAxis (q^m))) = Ideal.Quotient.mk z.asIdeal (yAxis (q^m))
      rw [show atOrigin q m hm (yAxis (q^m)) = 0 from eval_y _ _ _ _,map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr hy).symm
  have hsurj : Function.Surjective (atOrigin q m hm) := by
    intro u
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨algebraMap R (Node (q^m)) r,(atOrigin q m hm).commutes r⟩
  apply (RingHom.ker_isMaximal_of_surjective _ hsurj).eq_of_le z.isPrime.ne_top
  intro x hx'
  have H := DFunLike.congr_fun hcomp x
  change τ (atOrigin q m hm x) = Ideal.Quotient.mk z.asIdeal x at H
  change atOrigin q m hm x = 0 at hx'
  rw [hx',map_zero] at H
  exact Ideal.Quotient.eq_zero_iff_mem.mp H.symm

/-- Closedness of the literal double point over a DVR, even at the
thin-node terminal chart. -/
theorem maximal [IsDomain R] [IsDiscreteValuationRing R] (hq : Irreducible q) (hm : m ≠ 0)
    (z : PrimeSpectrum (Node (q^m))) (hx : xAxis (q^m) ∈ z.asIdeal)
    (hy : yAxis (q^m) ∈ z.asIdeal) : z.asIdeal.IsMaximal := by
  letI : (uniformizerIdeal q).IsMaximal := uniformizer_maximal q hq
  letI : Field (residue q) := Ideal.Quotient.field (uniformizerIdeal q)
  rw [← kernel q m hm z hx hy]
  apply RingHom.ker_isMaximal_of_surjective
  intro u
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective u
  exact ⟨algebraMap R (Node (q^m)) r,(atOrigin q m hm).commutes r⟩

/-- On the original thick chart, keep the exact strict old Rees centre
ideal I(q,d), not simply the support of a coordinate quotient. -/
theorem thick_read [IsDomain R] [IsDiscreteValuationRing R] (hq : Irreducible q) (d : ℕ)
    (z : PrimeSpectrum (Node (q^(d+2)))) (hx : xAxis (q^(d+2)) ∈ z.asIdeal)
    (hy : yAxis (q^(d+2)) ∈ z.asIdeal) :
    z.asIdeal = OriginalThickCentralReesChart318.I q d := by
  letI : (uniformizerIdeal q).IsMaximal := uniformizer_maximal q hq
  have hm : d+2 ≠ 0 := by omega
  have H := (kernel q (d+2) hm z hx hy).symm
  exact H.trans (OriginalR47LiteralNodeCentre318.kernel_eq q d)

end OriginalR47LiteralDoubleOrigin318

#print axioms OriginalR47LiteralDoubleOrigin318.q_mem
#print axioms OriginalR47LiteralDoubleOrigin318.kernel
#print axioms OriginalR47LiteralDoubleOrigin318.maximal
#print axioms OriginalR47LiteralDoubleOrigin318.thick_read
