module
public import AnchorAnisotropy
public section
namespace AuxiliaryCombinedAnchor318

/-- Combining the same nonzero binary value gives the homogeneous anchor.
The retained rational anisotropy theorem, not the sign of C or the B-side
alone, justifies its affine chart for both positive and negative C. -/
theorem representation_of_common_global_value (C t X Z T Y : ℚ)
    (ht : t≠0) (hA : X^2-2*Z^2=t) (hB : C*T^2-6*Y^2=t) :
    ∃ x y z : ℚ, x^2+6*y^2-2*z^2=C := by
  apply AnchorAnisotropy.rational_representation_of_homogeneous C
  refine ⟨X,Y,Z,T,?_,?_⟩
  · intro hzero
    obtain ⟨hX,_,hZ,_⟩ := hzero
    apply ht
    simpa only [hX,hZ,zero_pow (by decide : 2≠0),mul_zero,sub_zero] using hA.symm
  · linear_combination hA-hB

/-- Restore the original coefficient after its explicit signed squarefactor
and denominator normalization. The coefficient identity must be supplied
by the actual-r normalization, not assumed as a new local-global premise. -/
theorem scaled_representation (C c a : ℚ) (hc : c=a^2*C)
    (h : ∃ x y z : ℚ, x^2+6*y^2-2*z^2=C) :
    ∃ x y z : ℚ, x^2+6*y^2-2*z^2=c := by
  obtain ⟨x,y,z,he⟩ := h
  refine ⟨a*x,a*y,a*z,?_⟩
  rw [hc]
  linear_combination a^2*he

end AuxiliaryCombinedAnchor318
