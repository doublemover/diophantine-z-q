module
public import SelectedSameADyadicVerticalD2_318
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section

namespace OriginalIntegralFrameLocalize318
open SelectedSameADyadicVerticalD2_318
variable {K : Type*} [Field K] (A : Subring K) [IsFractionRing A K]

/-- In the original structural function field, no choice of a continuation
of an affine frame is needed after localizing the affine. -/
theorem derivation_agrees (D E : Derivation ℤ K K) (h : ∀ a : A,D (a:K)=E (a:K)) :
    D=E := by
  ext x
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective A x
  have eq (z:A) : D (algebraMap A K z)=E (algebraMap A K z) := h z
  rw [D.leibniz_div,E.leibniz_div,eq,eq]

def restrictD (V : Subring K) (D : Derivation ℤ K K) (h : ∀ x∈V, D x∈V) :
    Derivation ℤ V V where
  toLinearMap :=
    { toFun := fun z => ⟨D (z:K),h _ z.property⟩
      map_add' := fun x y => Subtype.ext (D.map_add (x:K) (y:K))
      map_smul' := fun n x => by
        apply Subtype.ext
        change D ((n • x : V):K) = ((n • (⟨D (x:K),h _ x.property⟩:V)):K)
        rw [show ((n • x : V):K)=n • (x:K) from map_zsmul V.subtype n x,
          show ((n • (⟨D (x:K),h _ x.property⟩:V)):K)=n • D (x:K) from
            map_zsmul V.subtype n _,D.map_smul] }
  map_one_eq_zero' := Subtype.ext D.map_one_eq_zero
  leibniz' x y := by
    apply Subtype.ext
    change D ((x:K)*(y:K))=(x:K)*D (y:K)+(y:K)*D (x:K)
    simpa only [smul_eq_mul] using D.leibniz (x:K) (y:K)

omit [IsFractionRing A K] in
theorem preserves_localization (M : Submonoid A) (V : Subring K) (hAV : A ≤ V)
    (loc : letI := (Subring.inclusion hAV).toAlgebra; IsLocalization M V)
    (D : Derivation ℤ K K) (hA : ∀ x∈A,D x∈A) : ∀ x∈V,D x∈V := by
  let : Algebra A V := (Subring.inclusion hAV).toAlgebra
  let : IsLocalization M V := loc
  intro x hx
  obtain ⟨⟨a,s⟩,he⟩ := IsLocalization.surj M (⟨x,hx⟩:V)
  have hf := congrArg V.subtype he
  change x*((s:A):K)=(a:K) at hf
  have su := IsLocalization.map_units V s
  let u := su.unit
  have huv : ((u:V):K)=((s:A):K) := congrArg V.subtype su.unit_spec
  have hin : (↑(u⁻¹):V)* (u:V)=1 := u.inv_mul
  have hci : ((↑(u⁻¹):V):K) * ((s:A):K)=1 := by
    rw [←huv]
    exact congrArg V.subtype hin
  have hn : ((s:A):K) ≠ 0 := by
    intro e
    rw [e,mul_zero] at hci
    exact zero_ne_one hci
  have hd := congrArg D hf
  rw [D.leibniz] at hd
  simp only [smul_eq_mul] at hd
  have hd' : D x=(D (a:K)-x*D ((s:A):K))*((↑(u⁻¹):V):K) := by
    apply mul_right_cancel₀ hn
    calc D x*((s:A):K) = D (a:K)-x*D ((s:A):K) := by linear_combination hd
         _ = _ := by rw [mul_assoc,hci,mul_one]
  rw [hd']
  exact V.mul_mem (V.sub_mem (hAV (hA _ a.property))
    (V.mul_mem hx (hAV (hA _ (s:A).property)))) (↑(u⁻¹):V).property

omit [IsFractionRing A K] in
theorem preserves_stalk (q : Ideal A) [q.IsPrime] (V : Subring K) (hAV : A ≤ V)
    (loc : letI := (Subring.inclusion hAV).toAlgebra; IsLocalization q.primeCompl V)
    (D : Derivation ℤ K K) (hA : ∀ x∈A,D x∈A) : ∀ x∈V,D x∈V :=
  preserves_localization A q.primeCompl V hAV loc D hA

/-- The field derivation of the induced relative Kaehler frame is the same
D on all fractions, not merely a comparison of absolute evaluations. -/
theorem field_localize (V : Subring K) [IsFractionRing V K] (D : Derivation ℤ K K)
    (hv : ∀ x∈V,D x∈V) :
    fractionDerivative V (restrictD V D hv).liftKaehlerDifferential = D := by
  apply derivation_agrees V
  intro a
  rw [fractionDerivative_apply,Derivation.liftKaehlerDifferential_comp_D]
  rfl

end OriginalIntegralFrameLocalize318
