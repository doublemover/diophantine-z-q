module
public import OriginalCovolumeIndex318
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public section
noncomputable section
namespace OriginalNormalHeightGenerator318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalIntegerSquaredNorm318
set_option maxHeartbeats 3000000

@[expose] def dotHom (n : Vector ℤ) : Vector ℤ →+ ℤ where
  toFun := dot n
  map_zero' := by simp [dot]
  map_add' u v := by simp [dot,mul_add] <;> ring

lemma dot_self_positive (n : Vector ℤ) (hn : n≠0) : 0<dot n n := by
  have he : embed n≠0 := by
    intro hz
    apply hn
    apply embed_injective
    rwa [embed_zero]
  have hr : (0:ℝ)<(dot n n:ℝ) := by
    rw [←inner_embed,real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr he)
  exact_mod_cast hr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Construct the POSITIVE generator of the original integer normal
functional on the ACTUAL lattice, together with an ACTUAL lattice point
attaining it. The cyclic image is not assumed saturated or primitive. -/
theorem actual_positive_generator (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (n : Vector ℤ) (hn : n≠0) :
    ∃ G : ℤ, 0<G ∧ ∃ u : Vector ℤ, u∈literalLattice p κ t ∧ dot n u=G ∧
      ∀ v : Vector ℤ, v∈literalLattice p κ t → G∣dot n v := by
  classical
  let L := literalLattice p κ t
  let H : AddSubgroup ℤ := L.map (dotHom n)
  let M := FixedSquarefreeCRT318.modulus p
  let u : Vector ℤ := ((M:ℤ)*n.1,(M:ℤ)*n.2.1,(M:ℤ)*n.2.2)
  have hu : u∈L := modulus_multiple_mem p κ t n
  have hdot : dot n u=(M:ℤ)*dot n n := by dsimp [u,dot]; ring
  have hpos : 0<dot n u := by
    rw [hdot]
    exact mul_pos (by exact_mod_cast FixedSquarefreeCRT318.modulus_positive p hp) (dot_self_positive n hn)
  have hmem : dot n u∈H := ⟨u,hu,rfl⟩
  obtain ⟨g,hg⟩ := exists_zsmul_surjective H
  have hdiv (v : Vector ℤ) (hv : v∈L) : (g:ℤ)∣dot n v := by
    obtain ⟨k,hk⟩ := hg ⟨dot n v,⟨v,hv,rfl⟩⟩
    have he := congrArg (fun x : H => (x:ℤ)) hk
    have he' : k*(g:ℤ)=dot n v := by simpa using he
    exact ⟨k,by simpa only [mul_comm] using he'.symm⟩
  have hg0 : (g:ℤ)≠0 := by
    intro hz
    have hh := hdiv u hu
    rw [hz,zero_dvd_iff] at hh
    omega
  obtain ⟨v,hv,hvg⟩ := g.2
  change dot n v=(g:ℤ) at hvg
  rcases lt_or_gt_of_ne hg0 with hneg | hpositive
  · refine ⟨-(g:ℤ),neg_pos.mpr hneg,-v,L.neg_mem hv,?_,?_⟩
    · have he := (dotHom n).map_neg v
      change dot n (-v)=-(g:ℤ)
      rw [he,hvg]
    · intro w hw
      exact neg_dvd.mpr (hdiv w hw)
  · exact ⟨(g:ℤ),hpositive,v,hv,hvg,hdiv⟩

/-- Any positive generator produced above is the LEAST positive normal
value, because every original normal value is its integer multiple. -/
lemma least_positive_value (G : ℤ) (hG : 0<G) (a : ℤ) (ha : 0<a) (hdiv : G∣a) : G≤a := by
  obtain ⟨k,hk⟩ := hdiv
  have hkpos : 0<k := by
    have hh : 0<G*k := by rwa [←hk]
    rcases mul_pos_iff.mp hh with ⟨_,hk'⟩ | ⟨hneg,_⟩
    · exact hk'
    · omega
  have hkone : 1≤k := hkpos
  simpa only [mul_one,←hk] using mul_le_mul_of_nonneg_left hkone hG.le

/-- The actual normal functional divided by ITS image generator is an
actual Euclidean-dual vector. The generator is not replaced by the norm,
modulus, determinant or coordinate gcd without proof. -/
theorem normal_generator_dual (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (n : Vector ℤ) (hn : n≠0) (G : ℤ) (hG : 0<G)
    (hdiv : ∀ v : Vector ℤ, v∈literalLattice p κ t → G∣dot n v) :
    (G:ℝ)⁻¹ • embed n∈Dual p κ t ∧ (G:ℝ)⁻¹ • embed n≠0 ∧
      ‖(G:ℝ)⁻¹ • embed n‖=‖embed n‖/(G:ℝ) := by
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  refine ⟨?_,?_,?_⟩
  · apply (dual_iff p κ t _).mpr
    intro v hv
    obtain ⟨k,hk⟩ := hdiv v hv
    refine ⟨k,?_⟩
    rw [real_inner_smul_left,inner_embed,hk,Int.cast_mul]
    field_simp [hGr.ne']
  · intro hz
    have hh := congrArg (fun w : E => (G:ℝ) • w) hz
    have he : embed n=0 := by simpa only [smul_smul,mul_inv_cancel₀ hGr.ne',one_smul,smul_zero] using hh
    apply hn
    apply embed_injective
    rwa [embed_zero]
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hGr]
    ring

end OriginalNormalHeightGenerator318
