module
public import OriginalReducedRectangleVolume318
public section
noncomputable section
namespace OriginalSieveFrame318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
open OriginalAnisotropicRectangle318 OriginalReciprocalMinimaRectangle318
open OriginalThirdMinimumTail318 OriginalAnisotropicResidueFibers318
set_option maxHeartbeats 4500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One actual whole original basis with its attained shortest-vector
controls. It is fixed before radius, sieve threshold or prime selection. -/
structure Frame (q : ι → ℕ) (κ : ℤ) (s : ∀ i, Option (ZMod (q i))) where
  u : Vector ℤ
  v : Vector ℤ
  w : Vector ℤ
  z : Vector ℤ
  basis : IntegralBasisTriple q κ s u v z
  first_second : ‖embed u‖≤‖embed v‖
  second_third : ‖embed v‖≤‖embed w‖
  inner_bound : |⟪embed u,embed v⟫|≤‖embed u‖^2/2
  last_bound : ‖embed z‖≤2*‖embed w‖
  third_minimal : ∀ y : Vector ℤ, y∈literalLattice q κ s →
    embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖

theorem frame_exists (q : ι → ℕ) (hq : ∀ i, (q i).Prime) (κ : ℤ)
    (s : ∀ i, Option (ZMod (q i))) : Nonempty (Frame q κ s) := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis q hq κ s
  exact ⟨⟨u,v,w,z,hb,huv,hvw,hip,hz,hwmin⟩⟩

variable {q : ι → ℕ} {κ : ℤ} {s : ∀ i, Option (ZMod (q i))}
@[expose] def Frame.firstRadius (d : Frame q κ s) (R : ℝ) := floorRadius (8*R/‖embed d.u‖)
@[expose] def Frame.secondRadius (d : Frame q κ s) (R : ℝ) := floorRadius (8*R/‖embed d.v‖)
@[expose] def Frame.thirdRadius (d : Frame q κ s) (R : ℝ) := floorRadius (4*R/‖embed d.w‖)

lemma interval_of_abs (A : ℕ) (c : ℤ) (hc : |c|≤(A:ℤ)) :
    c∈Finset.Icc (-(A:ℤ)) (A:ℤ) := Finset.mem_Icc.mpr (abs_le.mp hc)

/-- The original point itself is recovered after encoding in the actual
reciprocal-minimum rectangle, not merely its residue class. -/
theorem norm_rectangle_map (hq : ∀ i, (q i).Prime) (d : Frame q κ s)
    (R : ℝ) (hR : 0≤R) :
    ∃ f : NormPoints q κ s R → Rectangle (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R),
      Function.Injective f ∧ ∀ y, synthesis d.u d.v d.z (coordinates (f y))=y.1.1 := by
  classical
  let e := wholeEquiv q κ s d.u d.v d.z d.basis
  obtain ⟨h1,h2,h3⟩ := reciprocal_radii q hq κ s d.u d.v d.w d.z d.basis
    d.first_second d.second_third d.inner_bound d.last_bound d.third_minimal R hR
  have bounds (y : NormPoints q κ s R) :
      |(e.symm y.1).1|≤(d.firstRadius R:ℤ) ∧
      |(e.symm y.1).2.1|≤(d.secondRadius R:ℤ) ∧
      |(e.symm y.1).2.2|≤(d.thirdRadius R:ℤ) := by
    obtain ⟨ha,hb,hc⟩ := inverse_rectangle q hq κ s d.u d.v d.z d.basis
      d.first_second d.inner_bound R hR y.1 y.2
    exact ⟨ha.trans (by exact_mod_cast h1),hb.trans (by exact_mod_cast h2),hc.trans (by exact_mod_cast h3)⟩
  let f : NormPoints q κ s R → Rectangle (d.firstRadius R) (d.secondRadius R) (d.thirdRadius R) :=
    fun y => (⟨(e.symm y.1).1,interval_of_abs _ _ (bounds y).1⟩,
      ⟨(e.symm y.1).2.1,interval_of_abs _ _ (bounds y).2.1⟩,
      ⟨(e.symm y.1).2.2,interval_of_abs _ _ (bounds y).2.2⟩)
  have hf (y : NormPoints q κ s R) : synthesis d.u d.v d.z (coordinates (f y))=y.1.1 :=
    wholeEquiv_inverse q κ s d.u d.v d.z d.basis y.1
  refine ⟨f,?_,hf⟩
  intro a b he
  have hh := congrArg (fun c => synthesis d.u d.v d.z (coordinates c)) he
  rw [hf a,hf b] at hh
  exact Subtype.ext (Subtype.ext hh)

lemma normPoints_finite (hq : ∀ i, (q i).Prime) (R : ℝ) (hR : 0≤R) :
    Finite (NormPoints q κ s R) := by
  obtain ⟨d⟩ := frame_exists q hq κ s
  obtain ⟨f,hf,he⟩ := norm_rectangle_map hq d R hR
  exact Finite.of_injective f hf

end OriginalSieveFrame318
