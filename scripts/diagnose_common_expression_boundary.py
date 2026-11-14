#!/usr/bin/env python3
"""Hosted-only bounded structural observation of the original Common witness types."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_common_witness_conversion as previous
ci=previous.ci
DEPENDENCY_PINS = {'scripts/diagnose_common_witness_conversion.py': '315a122a14aa7ef7d753f0cec76fa638eb605109015ecd34ec8e14b27ee5a888', 'scripts/diagnose_diagonal_identity.py': 'f270b32bb08b551595e4b74cfbe3cb84ed26b3eef469894a7d4a7e5c574df7f2', 'scripts/diagnose_original_endpoint.py': '1d9e0fd76754d37372f24995469592a3707fe0d3ebf5c55518752449f80a3c00', 'scripts/check_progress_lean.py': 'a569e3952820fe0736a39e24db289c57d9d7fe87b5be6a4f4561f2b1ba551b63', '.github/workflows/progress-experiments.yml': '650c951f0f3bbc4053f65957e37d39a073059a2d001e0d9e862747d38af0a77e'}
STRUCTURAL_BODY = 'example : True := by\n  let lift := liftOfAlgHomUnit (k := R) (A := R[X]) (L := Laurent R)\n    (B := FiniteOrder R c) (T := OldOverlap R c) (X : R[X])\n    (finiteRestriction R c) (oldY R c)\n  let hX := finiteRestriction_X R c\n  run_tac\n    Lean.Elab.Tactic.withMainContext do\n      let emit : String → Lean.Elab.Tactic.TacticM Unit := fun line => do\n        let err ← IO.getStderr\n        err.putStrLn ("COMMON_EXPR " ++ line)\n        err.flush\n      let label : Lean.Expr → String := fun e =>\n        match e with\n        | .bvar n => s!"bvar {n}"\n        | .fvar id => s!"fvar {reprStr id}"\n        | .mvar id => s!"mvar {reprStr id}"\n        | .sort u => s!"sort {reprStr u}"\n        | .const n us => s!"const {n} levels={reprStr us}"\n        | .app _ _ => "app"\n        | .lam n _ _ bi => s!"lambda {n} binder={reprStr bi}"\n        | .forallE n _ _ bi => s!"forall {n} binder={reprStr bi}"\n        | .letE n _ _ _ nondep => s!"let {n} nondep={nondep}"\n        | .lit l => s!"literal {reprStr l}"\n        | .mdata _ _ => "metadata"\n        | .proj n i _ => s!"projection {n} index={i}"\n      emit s!"CONTROL same={Lean.Expr.equal (.const ``Nat []) (.const ``Nat [])} different={Lean.Expr.equal (.const ``Nat []) (.const ``Int [])}"\n      let partialType ← Lean.Meta.inferType (← Lean.Meta.getFVarFromUserName `lift)\n      let actual ← Lean.Meta.inferType (← Lean.Meta.getFVarFromUserName `hX)\n      let .forallE _ expected _ _ := partialType\n        | throwError "partial lift did not infer a direct forall witness binder"\n      emit s!"EXACT_STRUCTURAL_EQUAL {Lean.Expr.equal expected actual} (not a definitional-equality verdict)"\n      for (side, e) in [("expected", expected), ("actual", actual)] do\n        emit s!"ROOT {side} {label e.getAppFn} arity={e.getAppArgs.size}"\n        if e.isAppOfArity ``Eq 3 then\n          let args := e.getAppArgs\n          for i in [:3] do\n            let arg := args[i]!\n            emit s!"EQ_ARG {side} {i} {label arg.getAppFn} arity={arg.getAppArgs.size}"\n      let mut queue : Array (String × Lean.Expr × Lean.Expr) := #[("witness", expected, actual)]\n      let mut cursor := 0\n      let mut differences := 0\n      for _ in [:1024] do\n        if cursor >= queue.size || differences >= 8 then break\n        let (path, a, b) := queue[cursor]!\n        cursor := cursor + 1\n        if Lean.Expr.equal a b then continue\n        match a, b with\n        | .app f x, .app g y =>\n          queue := (queue.push (path ++ ".fn", f, g)).push (path ++ ".arg", x, y)\n        | .lam n t v bi, .lam n\' t\' v\' bi\'\n        | .forallE n t v bi, .forallE n\' t\' v\' bi\' =>\n          if n != n\' || bi != bi\' then\n            emit s!"BINDER_METADATA {path} left={label a} right={label b}"\n          queue := (queue.push (path ++ ".domain", t, t\')).push (path ++ ".body", v, v\')\n        | .letE n t v b nondep, .letE n\' t\' v\' b\' nondep\' =>\n          if n != n\' || nondep != nondep\' then\n            emit s!"LET_METADATA {path} left={label a} right={label b}"\n          queue := ((queue.push (path ++ ".type", t, t\')).push (path ++ ".value", v, v\')).push (path ++ ".body", b, b\')\n        | .mdata _ x, .mdata _ y =>\n          emit s!"METADATA_PAYLOAD_NOT_COMPARED {path}"\n          queue := queue.push (path ++ ".metadataBody", x, y)\n        | .proj n i x, .proj n\' i\' y =>\n          if n != n\' || i != i\' then\n            differences := differences + 1\n            emit s!"DIVERGENCE {path} left={label a} right={label b}"\n          else\n            queue := queue.push (path ++ ".projectionBody", x, y)\n        | _, _ =>\n          differences := differences + 1\n          emit s!"DIVERGENCE {path} left={label a} right={label b}"\n      emit s!"TRAVERSAL visited={cursor} queued={queue.size} divergences={differences} pending={decide (cursor < queue.size)}; cap=1024 pairs/8 atomic divergences; metadata not semantically compared"\n      emit "No unfolding, reduction, isDefEq, metavariable assignment, goal assignment or environment mutation was requested by this observer. Structural difference does not prove definitional inequality."\n  exact True.intro\n'

def check_dependencies():
    modules={'scripts/diagnose_common_witness_conversion.py':previous,
        'scripts/diagnose_diagonal_identity.py':previous.runner,
        'scripts/diagnose_original_endpoint.py':previous.runner.original,
        'scripts/check_progress_lean.py':ci}
    for name,module in modules.items():
        previous.require(previous.sha(Path(module.__file__))==DEPENDENCY_PINS[name],
            'Pinned diagnostic dependency changed: '+name)

def variants(source):
    original=previous.variants(source)
    prefix=original['exact_prefix']
    end='\nend IntegralOriginalCommonRestriction318\n'
    previous.require(prefix.endswith(end),'Original namespace suffix changed')
    structural=prefix[:-len(end)].replace('COMMON_WITNESS_DIAGNOSTIC exact_prefix',
        'COMMON_EXPRESSION_DIAGNOSTIC structural_witness')+STRUCTURAL_BODY+end
    return {'exact_prefix':prefix,'structural_witness':structural}

def validate(packet,output,hosted=True):
    check_dependencies()
    _,result_sha=previous.validate(packet,output,hosted)
    return variants((packet/(previous.MODULE+'.lean')).read_text()),result_sha

def main():
    parser=argparse.ArgumentParser();parser.add_argument('packet',choices=[previous.PACKET]);args=parser.parse_args()
    packet=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output=ci.ROOT/'build/progress-experiments'/args.packet
    cases,result_sha=validate(packet,output)
    env,version=ci.environment(ci.PROJECT,output/'lib')
    logs=output/'scratch-common-expression-diagnostics';logs.mkdir(exist_ok=False);rows=[]
    with tempfile.TemporaryDirectory(prefix='common-expression-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as temp:
        root=Path(temp)
        for name,text in cases.items():
            source=root/(name+'.lean');source.write_text(text);(logs/(name+'.lean.txt')).write_text(text)
            row=previous.runner.bounded_memory(source,root,env,logs/(name+'.log'))
            previous.require_no_compiled_artifacts(root)
            row['source_sha256']=hashlib.sha256(text.encode()).hexdigest();rows.append(row);print(json.dumps(row),flush=True)
        previous.require_no_compiled_artifacts(root)
        previous.require_no_compiled_artifacts(output/'lib',previous.MODULE)
    ci.write_json(logs/'DIAGNOSTIC.json',{'scope':'NON_ADMITTED_COMMON_EXPRESSION_BOUNDARY_ONLY',
        'packet':previous.PACKET,'packet_intake_sha256':previous.INTAKE_SHA,
        'original_source_sha256':previous.SOURCE_SHA,'full_result_sha256':result_sha,
        'toolchain':version,'seconds_per_probe':previous.SECONDS,'bytes_per_probe':previous.MAX_BYTES,
        'probe_wall_cap_sum_seconds':len(cases)*previous.SECONDS,
        'aggregate_runtime_note':'Up to 180 seconds of probe wall caps plus setup/cleanup, replacing the prior six-probe invocation; separate from production cap',
        'structural_observer_limits':'1024 queue pairs and eight atomic divergences; not a bound on work within inferType or Expr.equal; process bounds remain 90 seconds/2 MiB',
        'strict_flags':list(previous.EXPECTED_FLAGS),'compiled_artifact_absence_checked':True,
        'variants':rows,'full_packet_accepted':False,'baseline_or_experiment_accepted':False,
        'writes_olean':False,'production_source_changed':False})
if __name__=='__main__':main()
