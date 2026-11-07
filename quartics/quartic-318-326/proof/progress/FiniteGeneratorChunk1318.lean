module
public import FiniteSquareTest318
public section
namespace FiniteSquareTest318
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem leading_1 : CheckLeading 1 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 1"
theorem leading_2 : CheckLeading 2 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 2"
theorem leading_3 : CheckLeading 3 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 3"
theorem leading_4 : CheckLeading 4 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 4"
theorem leading_5 : CheckLeading 5 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 5"
theorem leading_6 : CheckLeading 6 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 6"
theorem leading_7 : CheckLeading 7 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 7"
theorem leading_8 : CheckLeading 8 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 8"
theorem leading_9 : CheckLeading 9 := by decide +kernel
run_cmd Lean.logInfo "FINITE_LEADING_PASS 9"
end FiniteSquareTest318
