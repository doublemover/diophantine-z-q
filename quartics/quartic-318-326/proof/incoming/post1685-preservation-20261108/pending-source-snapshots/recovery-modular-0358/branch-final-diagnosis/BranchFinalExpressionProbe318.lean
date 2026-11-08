module
import all FifthBranchCommonSection318
import all FifthCanonicalCommonRestriction318
import Lean
open Lean Meta Elab Command
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option pp.fullNames true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
run_cmd liftTermElabM do
  withLocalDeclD `j (mkApp (mkConst ``Fin) (mkNatLit 4)) fun j => do
    let lhsProof ← mkAppM ``FifthBranchCommonSection318.equality #[j]
    let rhsProof := mkConst ``FifthCanonicalCommonRestriction318.restrict
    let form ← mkAppM ``FifthBranchDifferential318.form #[j]
    let fn ← mkAppM ``BranchSectionExtension318.section_eq
      #[mkConst ``SourceTwistArithmetic318.units, j,
        mkConst ``FifthActualDifferential318.differential, form]
    let leftType ← inferType lhsProof
    let rightType ← inferType rhsProof
    let fnType ← inferType fn
    let expected ← forallTelescope fnType fun hs _ => do
      unless hs.size == 1 do throwError "Expected one proof argument, found {hs.size}"
      inferType hs[0]!
    let getSides (e : Expr) : MetaM (Expr × Expr) := do
      let e ← whnf e
      unless e.isAppOfArity ``Eq 3 do throwError "Not an equality: {e}"
      let a := e.getAppArgs
      return (a[1]!, a[2]!)
    let (ll,lr) ← getSides leftType
    let (rl,rr) ← getSides rightType
    let (el,er) ← getSides expected
    let seen ← IO.mkRef (#[] : Array (Expr × Expr))
    let rec diff (a b : Expr) (path : String) (fuel : Nat) : MetaM Nat := do
      let a := a.consumeMData
      let b := b.consumeMData
      let a := match a with | .letE _ _ v body _ => body.instantiate1 v | _ => a
      let b := match b with | .letE _ _ v body _ => body.instantiate1 v | _ => b
      if a == b then return fuel
      if (← isProof a) && (← isProof b) then return fuel
      if fuel == 0 then return 0
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if a.getAppFn == b.getAppFn && aa.size == ba.size && aa.size > 0 then
        let mut fuel := fuel
        for i in [:aa.size] do
          fuel ← diff aa[i]! ba[i]! (path++"."++toString i) fuel
        return fuel
      else
        let same ← withNewMCtxDepth <| isDefEq a b
        if (← seen.get).any (fun e => e.1 == a && e.2 == b) then return fuel
        seen.modify (·.push (a,b))
        logInfo m!"STRUCTURAL_DIFF {path} DEFINITIONALLY_EQUAL {same}\nACTUAL {a}\nEXPECTED {b}"
        return fuel-1
    let lc := (← whnf leftType).getAppArgs[0]!
    let rc := (← whnf rightType).getAppArgs[0]!
    let ec := (← whnf expected).getAppArgs[0]!
    for (name,a,b) in [("LEFT_INPUT",ll,el),("TRANS_MIDDLE",lr,rl),("RIGHT_INPUT",rr,er),
        ("LEFT_CARRIER",lc,ec),("TRANS_CARRIER",lc,rc),("RIGHT_CARRIER",rc,ec)] do
      logInfo m!"BEGIN {name} RAW_EQUAL {a == b}"
      let remaining ← diff a b "" 80
      logInfo m!"END {name} UNIQUE_DIFFS {80-remaining}"
