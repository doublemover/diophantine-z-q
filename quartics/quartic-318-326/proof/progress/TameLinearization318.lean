module
public import TameCoordinate318
public section
noncomputable section
open PowerSeries Function Finset
open TameCoordinate318
namespace TameLinearization318
set_option maxHeartbeats 0
variable {k:Type*} [Field k]

theorem orbit_tangent (F:k⟦X⟧) (hF:F.constantCoeff=0) (j:ℕ) :
    coeff 1 (orbit F hF j)=(coeff 1 F)^j := by
  induction j with
  | zero => simp [orbit_zero]
  | succ j ih => rw [orbit_succ,sigma_apply,coeff_one_subst F _ hF,ih,pow_succ]

theorem tangent_period (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ)
    (hperiod:orbit F hF n=X) : (coeff 1 F)^n=1 := by
  have h:=congrArg (coeff 1) hperiod
  simpa only [orbit_tangent,coeff_one_X] using h

@[expose] def weightedOrbit (F:k⟦X⟧) (hF:F.constantCoeff=0) (j:ℕ) : k⟦X⟧ :=
  ((coeff 1 F)⁻¹)^j • orbit F hF j

@[expose] def parameter (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ) : k⟦X⟧ :=
  (n:k)⁻¹ • ∑j∈range n,weightedOrbit F hF j

theorem weightedOrbit_coeff_one (F:k⟦X⟧) (hF:F.constantCoeff=0)
    (h1:coeff 1 F≠0) (j:ℕ) : coeff 1 (weightedOrbit F hF j)=1 := by
  simp [weightedOrbit,map_smul,orbit_tangent,smul_eq_mul,h1]

theorem parameter_constant (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ) :
    constantCoeff (parameter F hF n)=0 := by
  simp [parameter,weightedOrbit,orbit_constant]

theorem parameter_coeff_one (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F≠0)
    (n:ℕ) (hn:(n:k)≠0) : coeff 1 (parameter F hF n)=1 := by
  simp [parameter,map_smul,weightedOrbit_coeff_one F hF h1,hn]

theorem weightedOrbit_succ (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F≠0)
    (j:ℕ) : sigma F hF (weightedOrbit F hF j)=
      coeff 1 F • weightedOrbit F hF (j+1) := by
  simp only [weightedOrbit,map_smul,←orbit_succ,smul_smul,pow_succ]
  congr 1
  field_simp

theorem weightedOrbit_period (F:k⟦X⟧) (hF:F.constantCoeff=0) (n:ℕ)
    (hperiod:orbit F hF n=X) : weightedOrbit F hF n=weightedOrbit F hF 0 := by
  have hp:=tangent_period F hF n hperiod
  simp only [weightedOrbit,hperiod,inv_pow,hp,inv_one,one_smul,pow_zero,orbit_zero]

/-- Averaging with the actual tangent character gives a normalized formal
coordinate in which the finite-order substitution is linear. -/
theorem parameter_eigen (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F≠0)
    (n:ℕ) (hperiod:orbit F hF n=X) :
    (parameter F hF n).subst F=coeff 1 F • parameter F hF n := by
  have hsum : (∑j∈range n,weightedOrbit F hF (j+1))=∑j∈range n,weightedOrbit F hF j := by
    have ht:=Finset.sum_range_succ' (fun j=>weightedOrbit F hF j) n
    rw [Finset.sum_range_succ,weightedOrbit_period F hF n hperiod] at ht
    linear_combination -ht
  rw [←sigma_apply F (parameter F hF n) hF]
  simp only [parameter,map_smul,map_sum,weightedOrbit_succ F hF h1,←Finset.smul_sum,hsum]
  exact smul_comm _ _ _

/-- The actual compositional inverse exhibits conjugacy to the tangent
linear map, not just an abstract eigenparameter. -/
theorem conjugated_linear (F:k⟦X⟧) (hF:F.constantCoeff=0) (h1:coeff 1 F≠0)
    (n:ℕ) (hn:(n:k)≠0) (hperiod:orbit F hF n=X) :
    let H:=parameter F hF n
    let hu:IsUnit (coeff 1 H):=by rw [parameter_coeff_one F hF h1 n hn];exact isUnit_one
    PowerSeries.subst (H.substInvOfIsUnit hu) (PowerSeries.subst F H)=coeff 1 F • X := by
  dsimp only
  rw [parameter_eigen F hF h1 n hperiod,
    subst_smul (HasSubst.substInvOfIsUnit _ _),
    subst_substInvOfIsUnit_right _ (parameter_constant F hF n)]

/-- A nonzero finite period forces the tangent to be nonzero, and the
weighted average is a normalized linearizing parameter without any extra
nonzero-tangent assumption. -/
theorem exists_linearizing_parameter (F:k⟦X⟧) (hF:F.constantCoeff=0)
    (n:ℕ) (hn:(n:k)≠0) (hperiod:orbit F hF n=X) :
    ∃H:k⟦X⟧,constantCoeff H=0 ∧ coeff 1 H=1 ∧ H.subst F=coeff 1 F • H := by
  have hn0:n≠0 := by intro he;subst n;simp at hn
  have h1:coeff 1 F≠0 := by
    intro he
    have hp:=tangent_period F hF n hperiod
    rw [he,zero_pow hn0] at hp
    exact zero_ne_one hp
  exact ⟨parameter F hF n,parameter_constant F hF n,
    parameter_coeff_one F hF h1 n hn,parameter_eigen F hF h1 n hperiod⟩

end TameLinearization318
#print axioms TameLinearization318.parameter_eigen
#print axioms TameLinearization318.conjugated_linear

#print axioms TameLinearization318.exists_linearizing_parameter
