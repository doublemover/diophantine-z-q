module
public import BranchIntrinsicNaturality318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
def expected (c:Fin 4→ℚˣ) (j:Fin 4)
    (ω:KaehlerDifferential ℚ (ContactIntrinsicFrames318.BranchRing c j)):Prop:=
    (FamilyIntrinsicDifferentials318.omega (ContactIntrinsicDifferentials318.structureMap c)).presheaf.map
      (homOfLE (X:=(ContactGlobalSmooth318.Model c).Opens)
        (x:= (show Spec (CommRingCat.of (ContactKummerOrder318.OpenOrder c)) ⟶ ContactGlobalSmooth318.Model c from ContactOverlapIntrinsic318.embedding c) ''ᵁ ⊤)
        (y:= ContactIntrinsicFrames318.branchEmbedding c j ''ᵁ ⊤)
        (ContactFiniteTensorRestrictions318.branchLE c j)).op
      (IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (ContactIntrinsicFrames318.branchEmbedding c j)
        (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c j) ω)=
    IntrinsicChartSections318.sectionMap (Y:=ContactGlobalSmooth318.Model c) (R:=ℚ) (S:=ContactKummerOrder318.OpenOrder c) (ContactOverlapIntrinsic318.embedding c)
      (ContactIntrinsicDifferentials318.structureMap c) (ContactOverlapIntrinsic318.over_Q c)
      (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (T:=ContactKummerOrder318.OpenOrder c) (ContactOverlapAlgebraMaps318.branchMap c j) ω)
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let ty ← inferType (mkConst ``BranchIntrinsicNaturality318.naturality)
  forallTelescope ty fun xs actual => do
    let expect ← whnf (mkAppN (mkConst ``expected) xs)
    let rec diff (a b:Expr) (path:String) (fuel:Nat) : MetaM Nat := do
      let a := a.consumeMData
      let b := b.consumeMData
      let a := match a with | .letE _ _ v body _ => body.instantiate1 v | _ => a
      let b := match b with | .letE _ _ v body _ => body.instantiate1 v | _ => b
      if a == b then return fuel
      if !a.hasLooseBVars && !b.hasLooseBVars && (← isProof a) && (← isProof b) then return fuel
      if fuel == 0 then return 0
      match a,b with
      | .app af aa, .app bf ba =>
        let fuel ← diff af bf (path++"f") fuel
        diff aa ba (path++"a") fuel
      | .lam _ aty ab _, .lam _ bty bb _ =>
        let fuel ← diff aty bty (path++"t") fuel
        diff ab bb (path++"b") fuel
      | _,_ =>
        logInfo m!"DIFF {path}\nACTUAL {a}\nEXPECT {b}"
        return fuel-1
    let _ ← diff actual expect "" 30
    logInfo m!"ROOT_EQUAL {actual == expect}"
