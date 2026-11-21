import argparse,hashlib,re
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--donor',type=Path,help='the exact historical DetectorWeightPreparation318.lean')
args=parser.parse_args()
module_dir=Path(__file__).resolve().parent
LOCAL=module_dir/'ActualLinearQLiteralFoldCalibration318.lean'
suffix=Path('forward-actual-two-descent-root-divisor-orders-r5/DetectorWeightPreparation318.lean')
repo_prefix=Path('quartics/quartic-318-326/proof/experiments')
options=[module_dir.parent/suffix]
options.extend(p/'pel-integration43519890754/repo'/repo_prefix/suffix for p in module_dir.parents)
HIST=args.donor or next((p for p in options if p.is_file()),None)
if HIST is None:parser.error('detector donor not available; pass --donor /path/to/DetectorWeightPreparation318.lean')
assert hashlib.sha256(HIST.read_bytes()).hexdigest()=='3411a5bd2d9c604c31b88188d0fda451361799338c5fc71465767140adf7d0bd',HIST
h=HIST.read_text().split('def coefficients')[1].split('def weights')[0]
h=h[h.index('[(1,'):h.index(']\n')+1]
h=re.sub(r'\((\d),pair\s+\(([^()]*)\)\s+\(([^()]*)\)\)',r'(\1,(\2,\3))',h)
n=LOCAL.read_text().split('def coefficients')[1].split('def weights')[0]
n=n[n.index('[(1,'):n.index(']\n')+1]
clean=lambda s:re.sub(r'\s','',s)
assert clean(h)==clean(n),(clean(h),clean(n))
assert len(re.findall(r'\(\d,\(',n))==16
print('all 16 tags and 32 literal coordinate expressions byte-match after structural whitespace/pair normalization')
