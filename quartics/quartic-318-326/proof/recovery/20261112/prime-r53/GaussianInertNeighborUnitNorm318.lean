module
public import ActualPrimeEntryHeightObstruction318
public section
noncomputable section
namespace GaussianInertNeighborUnitNorm318
open GaussianNeighborNorms318 GaussianInertNeighborResidues318
variable (q : ℕ) [Fact q.Prime]
/-- A common DIVISOR of a neighboring count at an inert prime forces
specific Gaussian coordinates and norm one, not merely a local square. -/
lemma residues (h3 : q%4=3) (a b : ℤ) (hd : q∣minus a b ∨ q∣plus a b) :
    (b:ZMod q)=0 ∧ ((a:ZMod q)=1 ∨ (a:ZMod q)=-1) ∧
      (norm a b:ZMod q)=1 := by
  rcases hd with hd|hd
  · obtain ⟨ha,hb⟩:=(minus_iff q h3 a b).mp hd
    exact ⟨hb,Or.inl ha,by simp [GaussianFiniteNormResidues318.cast_norm,ha,hb]⟩
  · obtain ⟨ha,hb⟩:=(plus_iff q h3 a b).mp hd
    exact ⟨hb,Or.inr ha,by simp [GaussianFiniteNormResidues318.cast_norm,ha,hb]⟩
lemma prime_residue (h3 : q%4=3) (p : ℕ) (a b : ℤ)
    (hn : (p:ℤ)=a^2+b^2) (hd : q∣minus a b ∨ q∣plus a b) : (p:ZMod q)=1 := by
  have he : norm a b=p := by
    exact_mod_cast (norm_cast a b).trans hn.symm
  rw [←he]
  exact (residues q h3 a b hd).2.2
end GaussianInertNeighborUnitNorm318
