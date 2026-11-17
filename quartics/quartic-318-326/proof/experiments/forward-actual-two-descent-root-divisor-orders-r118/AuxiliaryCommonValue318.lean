module
public import LegendreHomogeneousAffine318
public section
namespace AuxiliaryCommonValue318

/-- A nonzero isotropic vector for the actual split quaternary form gives a
nonzero value represented by both binary sides. Zero initial common values
are handled constructively, not excluded by an additional local premise. -/
theorem nonzero_common_value {F : Type*} [Field F] [CharZero F]
    (C x z T y : F) (hC : C≠0)
    (hne : ¬(x=0 ∧ z=0 ∧ T=0 ∧ y=0))
    (he : x^2-2*z^2=C*T^2-6*y^2) :
    ∃ t X Z U V : F, t≠0 ∧ X^2-2*Z^2=t ∧ C*U^2-6*V^2=t := by
  by_cases ht : x^2-2*z^2=0
  · have hB : C*T^2-6*y^2=0 := he.symm.trans ht
    by_cases hA : x=0 ∧ z=0
    · have hbase : ¬(y=0 ∧ C*T=0 ∧ (0:F)=0) := by
        rintro ⟨hy,hCT,_⟩
        have hT : T=0 := (mul_eq_zero.mp hCT).resolve_left hC
        exact hne ⟨hA.1,hA.2,hT,hy⟩
      have hnorm : (C*T)^2-(6*C)*y^2-C*(0:F)^2=0 := by
        linear_combination C*hB
      obtain ⟨u,v,hu⟩ := LegendreHomogeneousAffine318.affine_of_homogeneous
        (6*C) C y (C*T) 0 (mul_ne_zero (by norm_num) hC) hbase hnorm
      refine ⟨1,1,0,u/C,v,by norm_num,by norm_num,?_⟩
      calc
        C*(u/C)^2-6*v^2=(u^2-(6*C)*v^2)/C := by field_simp [hC] <;> ring
        _=1 := by rw [hu]; exact div_self hC
    · have hbase : ¬(z=0 ∧ x=0 ∧ (0:F)=0) := by
        rintro ⟨hz,hx,_⟩
        exact hA ⟨hx,hz⟩
      have hnorm : x^2-2*z^2-C*(0:F)^2=0 := by simpa using ht
      obtain ⟨u,v,hu⟩ := LegendreHomogeneousAffine318.affine_of_homogeneous
        2 C z x 0 (by norm_num) hbase hnorm
      exact ⟨C,u,v,1,0,hC,hu,by ring⟩
  · exact ⟨x^2-2*z^2,x,z,T,y,ht,rfl,he.symm⟩

end AuxiliaryCommonValue318
