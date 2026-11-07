#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 - <<'CHECK'
import hashlib,json
from pathlib import Path
for f,h in json.loads(Path('verification.json').read_text())['sha256'].items():
 assert hashlib.sha256(Path(f).read_bytes()).hexdigest()==h,f
print('All frozen sources match.')
CHECK
mkdir -p .lake/build/lib/lean
lake env lean -Ddebug.skipKernelTC=false QuarticOptimization.lean -o .lake/build/lib/lean/QuarticOptimization.olean
lake env lean -Ddebug.skipKernelTC=false SparseQuartic.lean -o .lake/build/lib/lean/SparseQuartic.olean
lake env lean -Ddebug.skipKernelTC=false CircuitReplay.lean -o .lake/build/lib/lean/CircuitReplay.olean
lake env lean -Ddebug.skipKernelTC=false ExactDegree.lean -o .lake/build/lib/lean/ExactDegree.olean
lake env lean -Ddebug.skipKernelTC=false CoupledExponents.lean -o .lake/build/lib/lean/CoupledExponents.olean
lake env lean -Ddebug.skipKernelTC=false OddAnchor.lean -o .lake/build/lib/lean/OddAnchor.olean
lake env lean -Ddebug.skipKernelTC=false ScalarJacobi.lean -o .lake/build/lib/lean/ScalarJacobi.olean
lake env lean -Ddebug.skipKernelTC=false SingleFortyWeight.lean -o .lake/build/lib/lean/SingleFortyWeight.olean
lake env lean -Ddebug.skipKernelTC=false MixedElevenFortyOne.lean -o .lake/build/lib/lean/MixedElevenFortyOne.olean
lake env lean -Ddebug.skipKernelTC=false SixHelperWeights.lean -o .lake/build/lib/lean/SixHelperWeights.olean
lake env lean -Ddebug.skipKernelTC=false AffineAnchor.lean -o .lake/build/lib/lean/AffineAnchor.olean
lake env lean -Ddebug.skipKernelTC=false AnchorValueShear.lean -o .lake/build/lib/lean/AnchorValueShear.olean
lake env lean -Ddebug.skipKernelTC=false NestedInput.lean -o .lake/build/lib/lean/NestedInput.olean
lake env lean -Ddebug.skipKernelTC=false ConcreteQuadraticDomains.lean -o .lake/build/lib/lean/ConcreteQuadraticDomains.olean
lake env lean -Ddebug.skipKernelTC=false ReciprocalDeltaLog.lean -o .lake/build/lib/lean/ReciprocalDeltaLog.olean
lake env lean -Ddebug.skipKernelTC=false NormChainValuation.lean -o .lake/build/lib/lean/NormChainValuation.olean
lake env lean -Ddebug.skipKernelTC=false NormChainZero.lean -o .lake/build/lib/lean/NormChainZero.olean
lake env lean -Ddebug.skipKernelTC=false NormChainExtraction.lean -o .lake/build/lib/lean/NormChainExtraction.olean
lake env lean -Ddebug.skipKernelTC=false OddAffineInput.lean -o .lake/build/lib/lean/OddAffineInput.olean
lake env lean -Ddebug.skipKernelTC=false ArithmeticSeparation.lean -o .lake/build/lib/lean/ArithmeticSeparation.olean
lake env lean -Ddebug.skipKernelTC=false BaseWeightFusion.lean -o .lake/build/lib/lean/BaseWeightFusion.olean
lake env lean -Ddebug.skipKernelTC=false AcyclicWeightLowerBound.lean -o .lake/build/lib/lean/AcyclicWeightLowerBound.olean
lake env lean -Ddebug.skipKernelTC=false SharedScaleInverse.lean -o .lake/build/lib/lean/SharedScaleInverse.olean
lake env lean -Ddebug.skipKernelTC=false GreenBoundConstants.lean -o .lake/build/lib/lean/GreenBoundConstants.olean
lake env lean -Ddebug.skipKernelTC=false G8Nonvanishing.lean -o .lake/build/lib/lean/G8Nonvanishing.olean
lake env lean -Ddebug.skipKernelTC=false Height13DeltaLog.lean -o .lake/build/lib/lean/Height13DeltaLog.olean
lake env lean -Ddebug.skipKernelTC=false Height13RealLog.lean -o .lake/build/lib/lean/Height13RealLog.olean
lake env lean -Ddebug.skipKernelTC=false OrdinaryPoleNormalization.lean -o .lake/build/lib/lean/OrdinaryPoleNormalization.olean
lake env lean -Ddebug.skipKernelTC=false SixHeight13Weights.lean -o .lake/build/lib/lean/SixHeight13Weights.olean
lake env lean -Ddebug.skipKernelTC=false DegenerateDetector.lean -o .lake/build/lib/lean/DegenerateDetector.olean
lake env lean -Ddebug.skipKernelTC=false ConcreteG8Domain.lean -o .lake/build/lib/lean/ConcreteG8Domain.olean
lake env lean -Ddebug.skipKernelTC=false G4Nonvanishing.lean -o .lake/build/lib/lean/G4Nonvanishing.olean
lake env lean -Ddebug.skipKernelTC=false ConcreteG4Domain.lean -o .lake/build/lib/lean/ConcreteG4Domain.olean
lake env lean -Ddebug.skipKernelTC=false Height925DeltaLog.lean -o .lake/build/lib/lean/Height925DeltaLog.olean
lake env lean -Ddebug.skipKernelTC=false ThreeHelperPoleNormalization.lean -o .lake/build/lib/lean/ThreeHelperPoleNormalization.olean
lake env lean -Ddebug.skipKernelTC=false PadeNumeratorNonvanishing.lean -o .lake/build/lib/lean/PadeNumeratorNonvanishing.olean
lake env lean -Ddebug.skipKernelTC=false PadeDenominatorNonvanishing.lean -o .lake/build/lib/lean/PadeDenominatorNonvanishing.olean
lake env lean -Ddebug.skipKernelTC=false PadeAccuracy.lean -o .lake/build/lib/lean/PadeAccuracy.olean
lake env lean -Ddebug.skipKernelTC=false Pade21Domains.lean -o .lake/build/lib/lean/Pade21Domains.olean
lake env lean -Ddebug.skipKernelTC=false Pade21Accuracy.lean -o .lake/build/lib/lean/Pade21Accuracy.olean
lake env lean -Ddebug.skipKernelTC=false FiveHeight49Weights.lean -o .lake/build/lib/lean/FiveHeight49Weights.olean
lake env lean -Ddebug.skipKernelTC=false DegenerateContacts.lean -o .lake/build/lib/lean/DegenerateContacts.olean
lake env lean -Ddebug.skipKernelTC=false EvenDeltaValuation.lean -o .lake/build/lib/lean/EvenDeltaValuation.olean
lake env lean -Ddebug.skipKernelTC=false ValuationCurveParity.lean -o .lake/build/lib/lean/ValuationCurveParity.olean
lake env lean -Ddebug.skipKernelTC=false ValuationEvenNormChain.lean -o .lake/build/lib/lean/ValuationEvenNormChain.olean
lake env lean -Ddebug.skipKernelTC=false ValuationNormChainExtraction.lean -o .lake/build/lib/lean/ValuationNormChainExtraction.olean
lake env lean -Ddebug.skipKernelTC=false Height13WeightLowerBound.lean -o .lake/build/lib/lean/Height13WeightLowerBound.olean
lake env lean -Ddebug.skipKernelTC=false ValuationTraceSelection.lean -o .lake/build/lib/lean/ValuationTraceSelection.olean
lake env lean -Ddebug.skipKernelTC=false ConcreteValuationTrace.lean -o .lake/build/lib/lean/ConcreteValuationTrace.olean
lake env lean -Ddebug.skipKernelTC=false Pade21LocalError.lean -o .lake/build/lib/lean/Pade21LocalError.olean
lake env lean -Ddebug.skipKernelTC=false FinalComponentsAudit.lean > axioms-rechecked.log
python3 - <<'CHECK'
import json,re
from pathlib import Path
v=json.loads(Path('verification.json').read_text())
lines=re.sub(r'\n[ \t]+',' ',Path('axioms-rechecked.log').read_text()).splitlines()
assert len(lines)==v['auditedTheorems']
for l in lines:
 if 'depends on axioms:' in l:assert {x.strip() for x in l.split('[',1)[1].split(']')[0].split(',')}<=set(v['permittedBaseAxioms']),l
 else:assert 'does not depend on any axioms' in l,l
print('PASS: all component theorem audits.')
CHECK
