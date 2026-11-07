module
public import FiniteSquareTest318
public section
namespace FiniteGeneratorEnumeration318
open FiniteSquareTest318
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem rational_box : ∀(a:Fin 19)(b:Fin 9),
    CurveTest ((((a:ℕ):ℚ)-9)/((b:ℕ)+1)) 0 →
      Survivor ((((a:ℕ):ℚ)-9)/((b:ℕ)+1)) 0 := by decide +kernel

/-- The rational box deliberately permits unreduced fractions, so no
coprimality premise is needed to use its exhaustive result. -/
theorem bounded_rational (a:ℤ) (b:ℕ) (ha:-9≤a) (hA:a≤9) (hb:1≤b) (hB:b≤9)
    (hc:CurveTest ((a:ℚ)/(b:ℚ)) 0) : Survivor ((a:ℚ)/(b:ℚ)) 0 := by
  have h := rational_box ⟨(a+9).toNat,by omega⟩ ⟨b-1,by omega⟩
  have ha' : ((a+9).toNat:ℚ)-9=(a:ℚ) := by
    have he : ((a+9).toNat:ℤ)=a+9 := by omega
    exact_mod_cast (show ((a+9).toNat:ℤ)-9=a by omega)
  have hb' : ((b-1:ℕ):ℚ)+1=(b:ℚ) := by
    exact_mod_cast (show b-1+1=b by omega)
  have hh : CurveTest ((a:ℚ)/(b:ℚ)) 0 → Survivor ((a:ℚ)/(b:ℚ)) 0 := by
    simpa only [ha',hb'] using h
  exact hh hc

end FiniteGeneratorEnumeration318
