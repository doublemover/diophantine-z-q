module
public import Current326CoefficientBindingExpanded
public section
namespace Current326CoefficientBindingData
open Current326CoefficientBindingNormalize
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalized_data : normalize allExpansion = tableData := by
  decide +kernel

theorem table_eq_sos : evaluate monomial tableData = Current326Polynomial.P := by
  rw [← normalized_data, evaluate_normalize, sos_eq_expanded]

end Current326CoefficientBindingData
#print axioms Current326CoefficientBindingData.table_eq_sos
