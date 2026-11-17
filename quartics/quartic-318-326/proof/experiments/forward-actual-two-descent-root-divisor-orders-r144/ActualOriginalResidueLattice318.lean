module
public import ActualOriginalResiduePoisson318
public import ActualOriginalCongruenceCircle318
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public section
noncomputable section
namespace ActualOriginalResidueLattice318
open QuadricCRTAssembly318 ActualOriginalCongruenceCircle318 ActualOriginalIntegerTiling318
open scoped BigOperators
set_option maxHeartbeats 16000000

@[expose] def residueLift (q : ℕ) (r : Coordinates (ZMod q)) : Coordinates ℤ :=
  (((r.1.1.val : ℤ),(r.1.2.val : ℤ)),((r.2.1.1.val : ℤ),(r.2.1.2.val : ℤ)),(r.2.2.val : ℤ))

@[expose] def residuePoint (q : ℕ) (r : Coordinates (ZMod q)) (z : Coordinates ℤ) :
    Coordinates ℤ := residueLift q r+(q : ℤ) • z

lemma actual_residue_point_class (q : ℕ) [NeZero q] (r : Coordinates (ZMod q))
    (z : Coordinates ℤ) : originalResidue q (residuePoint q r z) = r := by
  simp [originalResidue,mapCoordinates,residuePoint,residueLift,smul_eq_mul,
    ZMod.natCast_self,ZMod.natCast_val]

lemma actual_residue_point_embedding (q : ℕ) (r : Coordinates (ZMod q)) (z : Coordinates ℤ) :
    integerEmbed (residuePoint q r z) = integerEmbed (residueLift q r)+(q : ℝ) • integerEmbed z := by
  simp [residuePoint,integerEmbed,smul_eq_mul]

lemma actual_residue_point_injective (q : ℕ) [NeZero q] :
    Function.Injective (fun p : Coordinates (ZMod q) × Coordinates ℤ => residuePoint q p.1 p.2) := by
  rintro ⟨r,z⟩ ⟨s,w⟩ he
  have hr := congrArg (originalResidue q) he
  simp only [actual_residue_point_class] at hr
  subst s
  have hz : (q : ℤ) • z = (q : ℤ) • w := add_left_cancel he
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  apply Prod.ext rfl
  apply Prod.ext
  · apply Prod.ext
    · apply mul_left_cancel₀ hq
      simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using congrArg (fun x : Coordinates ℤ => x.1.1) hz
    · apply mul_left_cancel₀ hq
      simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using congrArg (fun x : Coordinates ℤ => x.1.2) hz
  · apply Prod.ext
    · apply Prod.ext
      · apply mul_left_cancel₀ hq
        simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using congrArg (fun x : Coordinates ℤ => x.2.1.1) hz
      · apply mul_left_cancel₀ hq
        simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using congrArg (fun x : Coordinates ℤ => x.2.1.2) hz
    · apply mul_left_cancel₀ hq
      simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul] using congrArg (fun x : Coordinates ℤ => x.2.2) hz

lemma actual_residue_point_surjective (q : ℕ) [NeZero q] :
    Function.Surjective (fun p : Coordinates (ZMod q) × Coordinates ℤ => residuePoint q p.1 p.2) := by
  intro x
  obtain ⟨za,ha⟩ := (ZMod.intCast_eq_iff q x.1.1 (x.1.1 : ZMod q)).mp rfl
  obtain ⟨zb,hb⟩ := (ZMod.intCast_eq_iff q x.1.2 (x.1.2 : ZMod q)).mp rfl
  obtain ⟨zc,hc⟩ := (ZMod.intCast_eq_iff q x.2.1.1 (x.2.1.1 : ZMod q)).mp rfl
  obtain ⟨zd,hd⟩ := (ZMod.intCast_eq_iff q x.2.1.2 (x.2.1.2 : ZMod q)).mp rfl
  obtain ⟨zw,hw⟩ := (ZMod.intCast_eq_iff q x.2.2 (x.2.2 : ZMod q)).mp rfl
  refine ⟨(originalResidue q x,((za,zb),(zc,zd),zw)),?_⟩
  simp only [residuePoint,residueLift,originalResidue,mapCoordinates,
    Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul]
  exact Prod.ext (Prod.ext ha.symm hb.symm) (Prod.ext (Prod.ext hc.symm hd.symm) hw.symm)

/-- All original integer points, each exactly once, indexed by the actual
q^5 residue classes and their full integer translations. -/
@[expose] def residueLatticeEquiv (q : ℕ) [NeZero q] :
    Coordinates (ZMod q) × Coordinates ℤ ≃ Coordinates ℤ :=
  Equiv.ofBijective (fun p => residuePoint q p.1 p.2)
    ⟨actual_residue_point_injective q,actual_residue_point_surjective q⟩

lemma actual_residue_lattice_equiv_apply (q : ℕ) [NeZero q]
    (r : Coordinates (ZMod q)) (z : Coordinates ℤ) :
    residueLatticeEquiv q (r,z) = residuePoint q r z := rfl

/-- A genuine full-lattice reindexing and Fubini identity, applied only
after summability on the actual original integer lattice is known. -/
theorem actual_original_residue_tsum (q : ℕ) [NeZero q] (f : Coordinates ℤ → ℂ)
    (hf : Summable f) :
    (∑' x : Coordinates ℤ, f x) =
      ∑ r : Coordinates (ZMod q), ∑' z : Coordinates ℤ, f (residuePoint q r z) := by
  have hs := hf.comp_injective (residueLatticeEquiv q).injective
  calc
    (∑' x : Coordinates ℤ, f x) =
        ∑' p : Coordinates (ZMod q) × Coordinates ℤ, f (residueLatticeEquiv q p) :=
      ((residueLatticeEquiv q).tsum_eq f).symm
    _ = ∑' r : Coordinates (ZMod q), ∑' z : Coordinates ℤ, f (residuePoint q r z) := hs.tsum_prod
    _ = ∑ r : Coordinates (ZMod q), ∑' z : Coordinates ℤ, f (residuePoint q r z) := tsum_fintype _

end ActualOriginalResidueLattice318
