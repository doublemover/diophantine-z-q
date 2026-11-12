#!/usr/bin/env python3
"""Hosted-only actual tensor-face helper, specialization and final consumer checks."""
import argparse,hashlib,os,tempfile
from pathlib import Path
import diagnose_diagonal_identity as previous
ci=previous.ci
PACKET='contact-relative-site-descent-r57'
SOURCE_SHA='7e35791569b02fbb61e33001479298b09b6a15105aeec22a32b3b13335f98508'
CONSUMER_SHA='b1e39ad5506c0f29b1b0aff85d58468096dfc72db238f8ef44a84444ede0fbfd'
PRODUCER_PINS={'OriginalGeometricDiagonal318': '6a3c6fa0d3743425e41035f1eb94335b6807f4d130bddc4dc3582662596345c9', 'AffineSplitDiagonalTranspose318': 'cb4722bd1dfa305f5e2864faafd0f0f228d280fa9d5caf097f58842ececf05d6', 'SheafPathTransport318': '12dc3151cd2cb143979306bb29409feec098defc699ca1bb7f8faada91985634', 'ActualAffineSheafData318': '56edfcbb58c06d1a4aad0d77b5d090c8dee2fc9020487f31d9554da8c981cc84'}
def variants(source,consumer):
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_SHA
    assert hashlib.sha256(consumer.encode()).hexdigest()==CONSUMER_SHA
    helper=source.index('/-- Independently kernel-checkable affine path bridge')
    actual=source.index('variable (R S :')
    native=source.index('lemma native_face (')
    affine=source.index('/-- The ACTUAL affine-nerve specialization')
    final=source.index('/-- The exact original final declaration')
    end='\nend ActualAffineTensorTransport318\n'
    header='module\npublic import ActualAffineTensorTransport318\n'
    assert consumer.startswith(header)
    result={
      'generic_affine_transport_only':source[:actual]+end,
      'actual_native_square_only':source[:helper]+source[actual:affine]+end,
      'actual_affine_specialization_only':source[:native]+source[affine:final]+end,
      'actual_full_tensor_transport':source,
      'actual_downstream_tensor_laws':source+'\n'+consumer[len(header):]}
    for text in result.values():
        assert 'sorry' not in text and 'axiom ' not in text
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('packet',choices=[PACKET]);a=p.parse_args()
    if os.environ.get('GITHUB_ACTIONS')!='true' or not os.environ.get('RUNNER_TEMP'):
        raise RuntimeError('Hosted GitHub Actions only')
    output=ci.ROOT/'build/progress-experiments'/a.packet;lib=output/'lib'
    if not all((lib/(n+'.olean')).is_file() for n in PRODUCER_PINS):
        raise RuntimeError('Required genuinely compiled actual producers unavailable')
    folder=ci.ROOT/'quartics/quartic-318-326/proof/experiments'/a.packet
    for n,pin in PRODUCER_PINS.items():assert hashlib.sha256((folder/(n+'.lean')).read_bytes()).hexdigest()==pin
    source=(folder/'ActualAffineTensorTransport318.lean').read_text();consumer=(folder/'ActualAffineTensorLaws318.lean').read_text()
    env,version=ci.environment(ci.PROJECT,lib)
    logs=output/'scratch-tensor-transport-faces-diagnostics';logs.mkdir(exist_ok=False)
    rows=[]
    with tempfile.TemporaryDirectory(prefix='tensor-transport-genuine-',dir=os.environ['RUNNER_TEMP']) as folder:
        root=Path(folder)
        for name,text in variants(source,consumer).items():
            f=root/(name+'.lean');f.write_text(text)
            row=previous.bounded_memory(f,root,env,logs/(name+'.log'))
            row.update(source_sha256=hashlib.sha256(text.encode()).hexdigest(),contains_sorry=False);rows.append(row)
    ci.write_json(logs/'DIAGNOSTIC.json',dict(scope='GENERIC_BRIDGE_ACTUAL_NATIVE_AND_AFFINE_SPECIALIZATIONS_EXACT_FINAL_AND_DOWNSTREAM',
      source_sha256=SOURCE_SHA,consumer_sha256=CONSUMER_SHA,producer_pins=PRODUCER_PINS,toolchain=version,variants=rows,
      baseline_or_experiment_accepted=False,writes_olean=False))
if __name__=='__main__':main()
