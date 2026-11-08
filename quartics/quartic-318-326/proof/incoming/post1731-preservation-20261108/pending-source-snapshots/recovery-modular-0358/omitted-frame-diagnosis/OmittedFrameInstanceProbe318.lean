module
import all BranchGlobalDifferentialRestriction318
import all CharacterBranchActualRestriction318
import all FrameUnitMultiple318
import Lean
open Lean Meta Elab Command
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
set_option pp.fullNames true
set_option pp.explicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
run_cmd liftTermElabM do
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit 4)) fun i => do
    let c := mkConst ``SourceTwistArithmetic318.units
    let formFn ← mkAppM ``BranchGlobalDifferentialRestriction318.form #[i]
    forallTelescopeReducing (← inferType formFn) fun xs _ => do
      unless xs.size == 1 do throwError "Unexpected form arity {xs.size}"
      let s := xs[0]!
      let ht ← mkAppM ``CharacterDifferentialInvariants318.Fixed #[i,s]
      withLocalDeclD `h ht fun h => do
        let e ← mkAppM ``ContactDifferentialFrames318.sourceLocalizationFrame #[c,i]
        let t ← mkAppM ``BranchDifferentialDivisibility318.t #[c,i]
        let k ← mkAppM ``CharacterBranchLocalForm318.unitCoefficient #[i,i]
        let ω := mkApp formFn s
        let ω₀ ← mkAppM ``CharacterBranchLocalForm318.form #[i,i]
        let hd ← mkAppM ``BranchDifferentialDivisibility318.coordinate_normalized #[c,i]
        let hdTy ← whnf (← inferType hd)
        unless hdTy.isAppOfArity ``Eq 3 do throwError "Unexpected normalized equality"
        let d := hdTy.getAppArgs[1]!.getAppArgs.back!
        let hk ← mkAppM ``CharacterBranchLocalForm318.unitCoefficient_unit #[i,i]
        let hf ← mkAppM ``BranchGlobalDifferentialRestriction318.invariant_factorization #[i,s,h]
        let h₀ ← mkAppM ``CharacterBranchLocalForm318.omitted_frame_value #[i]
        let fn ← mkAppM ``FrameUnitMultiple318.of_factorization #[e,t,k,ω,ω₀,d]
        logInfo "GENERIC APPLICATION ELABORATED"
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
            let mut f := fuel
            for j in [:aa.size] do f ← diff aa[j]! ba[j]! (path++"."++toString j) f
            return f
          else
            let ap := (toString (← ppExpr a)).take 1100
            let bp := (toString (← ppExpr b)).take 1100
            logInfo m!"STRUCTURAL_DIFF {path}\nACTUAL {ap}\nEXPECTED {bp}"
            logInfo m!"DEFINITIONAL_CHECK_NOT_REPEATED {path}"
            return fuel-1
        let ty ← inferType fn
        forallTelescope ty fun ys _ => do
          unless ys.size == 4 do throwError "Expected four proof inputs, found {ys.size}"
          for j in [:ys.size] do
            let actual ← inferType (#[hk,hd,hf,h₀][j]!)
            let expected ← inferType ys[j]!
            logInfo m!"BEGIN ARG {j} RAW_EQUAL {actual == expected}"
            let f ← diff actual expected "" 32
            logInfo m!"END ARG {j} DIFFS {32-f}"
        let args := fn.getAppArgs
        for j in [:min 5 args.size] do
          logInfo m!"GENERIC_IMPLICIT {j} {(toString (← ppExpr args[j]!)).take 4000}"
