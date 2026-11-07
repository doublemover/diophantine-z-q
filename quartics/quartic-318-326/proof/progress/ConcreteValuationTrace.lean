module
public import ValuationTraceSelection
public import ConcreteG8Domain
public section
namespace ConcreteValuationTrace
open ConcreteG8Domain

theorem source_trace_equation (w0 w1 n : ℚ)
    (h : 2*w0*n=w0^2-2*w1^2) :
    pair n 0*(pair w0 w1+pair w0 (-w1))=pair w0 w1*pair w0 (-w1) := by
  ext <;> simp [pair,pow_two] <;> nlinarith

theorem source_one_place (v : AddValuation K (WithTop ℤ)) (w0 w1 n : ℚ)
    (R a b c : ℤ) (hw : v (pair w0 w1)=a)
    (hb : v (pair w0 (-w1))=b) (hn : v (pair n 0)=c)
    (heq : 2*w0*n=w0^2-2*w1^2) (hpole : 0<2*c+R) :
    0<2*a+R ∨ 0<2*b+R :=
  ValuationTraceSelection.one_place v _ _ _ R a b c hw hb hn
    (source_trace_equation w0 w1 n heq) hpole
end ConcreteValuationTrace
