#!/usr/bin/env python3
"""Hosted-only nonadmitted canonical-overlap naturality probes.
Replaces the previous three transport processes with two 90-second probes.
The production theorem, its inputs, source and 180-second bound are unchanged.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import diagnose_picard_object_transport as previous

fragments, isolation = previous.fragments, previous.isolation
ci, runner = previous.ci, previous.runner
require, sha = previous.require, previous.sha
PACKET, MODULE = previous.PACKET, previous.MODULE
SECONDS, MAX_BYTES = previous.SECONDS, previous.MAX_BYTES
PREVIOUS_SCRIPT_SHA = 'feacc9e0dd306e8e4048608d3a1423b7fbc8373109f81f2e0f483059efb8dd8a'
HISTORY_SHA = 'f7a69220ade551895432a913bc5b76925978f733d9ffb77ef038356f3db4ca38'
HISTORY = Path(__file__).parent/'diagnostic_evidence/picard_transport_43603177874.json'
NAMES = ['concrete_canonical_overlap_naturality', 'assembled_naturality_transfer']
ARGS = previous.ARGS
V, W, E, D, HOBJ, HCMP = previous.V, previous.W, previous.E, previous.D, previous.HOBJ, previous.HCMP
CISO = '(eqToIso '+HOBJ+')'
F = '(Scheme.Modules.pullback (baseMap R S))'
P = '(Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S)))'
Q = '(Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S)))'
AV = '(CanonicalSheafOverlap318.actual '+V+' (baseMap R S))'
AW = '(CanonicalSheafOverlap318.actual '+W+' (baseMap R S))'
NAT_NAME = 'reconstructed_canonical_overlap_naturality'
NAT_GENERIC = '''
/-- Scratch-only naturality of the SAME two path-isomorphism components. -/
private lemma canonical_actual_naturality {B U : Scheme.{u}} (f : U ⟶ B)
    {V W : B.Modules} (c : V ⟶ W) :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first f)).map
        ((Scheme.Modules.pullback f).map c) ≫ CanonicalSheafOverlap318.actual W f =
      CanonicalSheafOverlap318.actual V f ≫
        (Scheme.Modules.pullback (ActualOverlapDiagram318.second f)).map
          ((Scheme.Modules.pullback f).map c) := by
  have h₀ := (PullbackPathComposition318.iso (ActualOverlapDiagram318.first f)
    f (ActualOverlapDiagram318.first f ≫ f) rfl).hom.naturality c
  have h₁ := (PullbackPathComposition318.iso (ActualOverlapDiagram318.second f)
    f (ActualOverlapDiagram318.first f ≫ f)
    (ActualOverlapDiagram318.edge_condition f).symm).inv.naturality c
  simp only [Functor.comp_map] at h₀ h₁
  unfold CanonicalSheafOverlap318.actual CanonicalSheafOverlap318.overlap
  rw [← Category.assoc,h₀,Category.assoc,h₁,← Category.assoc]
'''
TRANSFER_GENERIC = '''
/-- Scratch-only transport by an actual base isomorphism and naturality.
No dependent object-equality eliminator or carrier substitution is used. -/
private lemma conjugation_of_base_iso_naturality
    {C U D : Type*} [Category C] [Category U] [Category D]
    (F : C ⥤ U) (P Q : U ⥤ D) {V W : C} {N : U}
    (c : V ≅ W) (e : F.obj V ≅ N) (d : F.obj W ≅ N)
    (he : F.mapIso c ≪≫ d = e)
    (a : P.obj (F.obj V) ⟶ Q.obj (F.obj V))
    (b : P.obj (F.obj W) ⟶ Q.obj (F.obj W))
    (τ : P.obj N ⟶ Q.obj N)
    (hn : P.map (F.map c.hom) ≫ b = a ≫ Q.map (F.map c.hom))
    (hd : P.map d.inv ≫ b ≫ Q.map d.hom = τ) :
    P.map e.inv ≫ a ≫ Q.map e.hom = τ := by
  let k := F.mapIso c
  have hk : P.map k.inv ≫ P.map k.hom = 𝟙 _ := by
    calc
      _ = P.map (k.inv ≫ k.hom) := (P.map_comp _ _).symm
      _ = P.map (𝟙 _) := congrArg (fun t => P.map t) k.inv_hom_id
      _ = 𝟙 _ := P.map_id _
  have hc : P.map k.inv ≫ a ≫ Q.map k.hom = b := by
    calc
      _ = P.map k.inv ≫ (a ≫ Q.map k.hom) := Category.assoc _ _ _
      _ = P.map k.inv ≫ (P.map k.hom ≫ b) :=
        congrArg (fun t => P.map k.inv ≫ t) hn.symm
      _ = (P.map k.inv ≫ P.map k.hom) ≫ b := (Category.assoc _ _ _).symm
      _ = b := by rw [hk,Category.id_comp]
  have hcomp :
      P.map (d.inv ≫ k.inv) ≫ a ≫ Q.map (k.hom ≫ d.hom) =
        P.map d.inv ≫ (P.map k.inv ≫ a ≫ Q.map k.hom) ≫ Q.map d.hom := by
    simp only [Functor.map_comp,Category.assoc]
  rw [← he]
  change P.map (d.inv ≫ k.inv) ≫ a ≫ Q.map (k.hom ≫ d.hom) = τ
  rw [hcomp,hc]
  exact hd
'''

def marker(name):
    return ('\nrun_cmd Lean.Elab.Command.liftIO do\n  let out ← IO.getStderr\n'
            '  out.putStrLn "PICARD_NATURALITY_'+name+'_COMMAND_END"\n  out.flush\n')

def variants(source):
    prefix, original, statement, native, inner, a, b, old = fragments.fragments(source)
    header, conclusion = statement.split(' :\n')
    nheader = header.replace('private lemma reconstructed_actual_overlap','private lemma '+NAT_NAME)
    nconclusion = ('    '+P+'.map ('+F+'.map '+CISO+'.hom) ≫\n      '+AW+' =\n'
                   '      '+AV+' ≫ '+Q+'.map ('+F+'.map '+CISO+'.hom)')
    ndecl = (nheader+' :\n'+nconclusion+' := by\n'+fragments.body_marker('CANONICAL_NATURALITY_ENTER')+
             '  exact canonical_actual_naturality (baseMap R S) '+CISO+'.hom\n'+
             fragments.body_marker('CANONICAL_NATURALITY_EXIT'))
    body = ('  exact conjugation_of_base_iso_naturality\n'
            '    '+F+'\n    '+P+'\n    '+Q+'\n'
            '    '+CISO+'\n    '+E+'\n    '+D+'\n    '+HCMP+'\n'
            '    '+AV+'\n    '+AW+'\n    τ\n'
            '    ('+NAT_NAME+' '+ARGS+' τ hσ)\n    ('+fragments.A_CALL+')\n')
    assembled = (statement+' := by\n'+fragments.body_marker('NATURALITY_ASSEMBLED_ENTER')+
                 body+fragments.body_marker('NATURALITY_ASSEMBLED_EXIT'))
    require(assembled.split(' := by\n',1)[0]==statement,'Original statement changed')
    texts = [prefix+NAT_GENERIC+marker('AFTER_GENERIC_NATURALITY')+ndecl,
             prefix+NAT_GENERIC+TRANSFER_GENERIC+marker('AFTER_GENERIC_LEMMAS')+
             a+marker('AFTER_NATIVE_A')+ndecl+marker('AFTER_CONCRETE_NATURALITY')+assembled]
    cases={n:t+marker(n)+isolation.END for n,t in zip(NAMES,texts)}
    for n,t in cases.items():
        for token in ['sorry','axiom ','(hObject :','(hComparison :','(hA :',isolation.FORBIDDEN_MARKER]:
            require(token not in t,'Unexpected premise/placeholder/production wrapper')
        require(t.startswith(prefix),'Original prefix changed')
    return cases

def history(source,path=HISTORY):
    require(path.is_file() and sha(path)==HISTORY_SHA,'Historical artifact bundle changed')
    j=json.loads(path.read_text())
    require(j['artifact']['id']==14117419334 and j['artifact']['workflow_run']['id']==43603177874,
            'Historical official artifact changed')
    require(j['artifact']['digest']=='sha256:a4a6911b16ef273424191a272fb965bfe035e885f5486e18945e80bce3489d42',
            'Historical official artifact digest changed')
    rec=j['diagnostic'];cases=previous.variants(source)
    for key,value in [('scope','NON_ADMITTED_EXACT_PICARD_OBJECT_TRANSPORT_ONLY'),
        ('packet',PACKET),('packet_intake_sha256',isolation.INTAKE_SHA),
        ('packet_application_sha256',isolation.APPLICATION_SHA),
        ('original_source_sha256',isolation.SOURCE_SHA),('seconds_per_probe',SECONDS),('bytes_per_probe',MAX_BYTES)]:
        require(rec.get(key)==value,'Historical binding changed: '+key)
    for key in ['full_packet_accepted','baseline_or_experiment_accepted','writes_olean',
                'production_source_changed','production_limits_changed']:
        require(rec.get(key) is False,'Historical admission/production boundary changed')
    rows=rec['variants'];require([r['variant'] for r in rows]==previous.NAMES,'Historical cases changed')
    for index,row in enumerate(rows):
        n=row['variant'];text=j['specimens'][n];log=j['logs'][n]
        require(text==cases[n] and hashlib.sha256(text.encode()).hexdigest()==row['source_sha256'],
                'Historical specimen changed')
        require(row['admitted'] is False and row['proof_acceptance'] is False and row['contains_sorry'] is False,
                'Historical admission detected')
        require(row['exact_object_comparison_A_are_extra_diagnostic_inputs']==(index==0),
                'Historical premise classification changed')
        expected=(0,None) if index==1 else (-9,'SCRATCH_WALL_LIMIT')
        require((row['exit_code'],row['limit'])==expected,'Historical outcome changed')
        end='PICARD_TRANSPORT_'+n+'_COMMAND_END'
        require((end in log)==(index==1),'Historical command frontier changed')
        if index!=1:require(log.endswith('\nSCRATCH_WALL_LIMIT\n'),'Historical wall-limit suffix missing')
        require(hashlib.sha256(log.encode()).hexdigest()==j['log_sha256'][n],'Historical log changed')
    return sha(path)

def validate(packet,output,hosted=True):
    require(sha(Path(previous.__file__))==PREVIOUS_SCRIPT_SHA,'Prior transport script changed')
    _,result_sha,log_sha,prior_sha=previous.validate(packet,output,hosted=hosted)
    source=(packet/(MODULE+'.lean')).read_text()
    history_sha=history(source)
    return variants(source),result_sha,log_sha,prior_sha,history_sha

def main():
    parser=argparse.ArgumentParser();parser.add_argument('packet',choices=[PACKET]);args=parser.parse_args()
    packet=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/args.packet
    output=ci.ROOT/'build/progress-experiments'/args.packet
    cases,result_sha,log_sha,prior_sha,history_sha=validate(packet,output)
    env,version=ci.environment(ci.PROJECT,output/'lib')
    logs=output/'scratch-picard-naturality';logs.mkdir(exist_ok=False);rows=[]
    with tempfile.TemporaryDirectory(prefix='picard-naturality-nonadmitted-',dir=os.environ['RUNNER_TEMP']) as directory:
        root=Path(directory)
        for name,text in cases.items():
            source=root/(name+'.lean');source.write_text(text);(logs/(name+'.lean.txt')).write_text(text)
            row=runner.bounded_memory(source,root,env,logs/(name+'.log'))
            require(not any(p.is_file() and any(p.name.endswith(s) for s in ci.SUFFIXES)
                            for p in root.rglob('*')),'Unexpected compiled scratch artifact')
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False,
                       extra_diagnostic_inputs=False,admitted=False,proof_acceptance=False)
            rows.append(row);print(json.dumps(row),flush=True)
    ci.write_json(logs/'DIAGNOSTIC.json',{
        'scope':'NON_ADMITTED_EXACT_PICARD_NATURALITY_ONLY','packet':PACKET,
        'packet_intake_sha256':isolation.INTAKE_SHA,'packet_application_sha256':isolation.APPLICATION_SHA,
        'original_source_sha256':isolation.SOURCE_SHA,'full_result_sha256':result_sha,
        'production_log_sha256':log_sha,'current_prior_fragments_result_sha256':prior_sha,
        'historical_object_transport_bundle_sha256':history_sha,
        'toolchain':version,'seconds_per_probe':SECONDS,'bytes_per_probe':MAX_BYTES,
        'maximum_additional_scratch_wall_seconds':2*SECONDS,'total_scheduled_site_scratch_cap_seconds':810,
        'replaces_previous_three_transport_processes':True,'variants':rows,
        'full_packet_accepted':False,'baseline_or_experiment_accepted':False,'writes_olean':False,
        'production_source_changed':False,'production_limits_changed':False,
        'interpretation':'Concrete canonical overlap naturality versus assembled base-isomorphism conjugation, retaining the exact original line/comparison and native A. No new premises or dependent object-equality eliminator in the new proofs. Both are nonadmitted diagnostics. Markers/timing rows are not kernel-completion evidence and missing rows do not uniquely identify an active phase.'})
if __name__=='__main__':main()

