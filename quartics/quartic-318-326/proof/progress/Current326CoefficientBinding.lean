module
public import Current326CoefficientBindingData
public section
namespace Current326CoefficientBinding

/-- Standard integer polynomial interpretation of the literal 3157-entry table.
The entries are encoded in tableChunk0 through tableChunk49 in Expanded.
JSON SHA256: d22173ff9a4cfd5b60318597a136036b4722893d7ca6e9a1e7694014061a9b73.
Each monomial is a finite product of coordinate variables; each integer
coefficient acts by integer scalar multiplication in the polynomial ring. -/
@[expose] noncomputable def tablePolynomial : MvPolynomial (Fin 326) ℤ :=
  Current326CoefficientBindingNormalize.evaluate
    Current326CoefficientBindingData.monomial Current326CoefficientBindingData.tableData

theorem table_eq_sos : tablePolynomial = Current326Polynomial.P :=
  Current326CoefficientBindingData.table_eq_sos

end Current326CoefficientBinding
#print axioms Current326CoefficientBinding.table_eq_sos
