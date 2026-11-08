module
import all CompletedAdditionAssociativityTest318
import Lean
open Lean Elab Command in
run_cmd do
 let e ← getEnv
 for i in [:e.header.modules.size] do
  if e.header.modules[i]!.module == `CompletedAdditionAssociativityTest318 then
   for n in e.header.moduleData[i]!.constNames do
    logInfo m!"DECL: {n}"
#check CompletedAdditionAssociativityTest318.point1
#check CompletedAdditionAssociativityTest318.field_test
