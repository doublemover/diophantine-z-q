from pathlib import Path
import hashlib,json,shutil,difflib,sys,subprocess
w=Path(__file__).resolve().parent;r=w.parent/'pel-followup43603177874/repo';head='4c5562395a9891e0d79fa5808926ebf9b2781470';ex=r/'quartics/quartic-318-326/proof/experiments';c=w/'candidates';c.mkdir(exist_ok=True);(c/'primary').mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();write=lambda p,d:p.write_text(json.dumps(d,indent=2)+'\n')
base=ex/'forward-actual-two-descent-root-divisor-orders-r16';old=base/'ScalarSmallPrimePreparation318.lean';assert sha(old)=='e808d212ea6cd4edc8fe7ca8b839b19b80480adfacddf0671d227ce6ee8bec9e'
for kind,name in [('descent','forward-actual-two-descent-root-divisor-orders-r16'),('weighted','forward-original-weighted-weyl-r22-replay-r16')]:
 p=ex/name;assert (p/old.name).read_bytes()==old.read_bytes()
 for f in ['ScalarSmallPrimePreparation318.lean','intake.json','APPLICATION.json']:
  shutil.copyfile(p/f,c/(kind+'.before.'+f))
new=old.read_text();helper='''/-- The elementary unit facts are proved before the large integer-shape
context is introduced. The actual multiplier and all three forms are unchanged. -/
private lemma multiplier_units (k₂ k₃ k₁₇ : ℤ) :
    (¬(2:ℤ)∣(1+8*k₂)) ∧ (¬(3:ℤ)∣(1+3*k₃)) ∧ (¬(17:ℤ)∣(8+17*k₁₇)) := by
  constructor
  · omega
  constructor <;> omega

'''
needle='lemma actual_multiplier_values (a : ℤ) :';assert new.count(needle)==1;new=new.replace(needle,helper+needle)
needle='  obtain ⟨⟨k₂,h₂⟩,⟨k₃,h₃⟩,⟨k₁₇,h₁₇⟩⟩ := integerA_shapes a\n';assert new.count(needle)==1;new=new.replace(needle,needle+'  have hu := multiplier_units k₂ k₃ k₁₇\n')
for p,e,k,term,proof in [(2,4,'₂','1+8*k₂','hu.1'),(3,2,'₃','1+3*k₃','hu.2.1'),(17,2,'₁₇','8+17*k₁₇','hu.2.2')]:
 s=f'convert value_scaled_unit {p} {e} ({term}) (by omega) using 1';assert new.count(s)==1;new=new.replace(s,f'convert value_scaled_unit {p} {e} ({term}) {proof} using 1')
(c/old.name).write_text(new);(c/(old.name+'.diff')).write_text(''.join(difflib.unified_diff(old.read_text().splitlines(True),new.splitlines(True),fromfile='before/'+old.name,tofile='after/'+old.name)))
for n in ['ScalarPackedLocalUnit318','ScalarPolePreparation318','ScalarForwardWitness318','AllScalarSupportPreparation318','ScalarSmallPrimeProgression318']:
 shutil.copyfile(base/(n+'.lean'),c/'primary'/(n+'.lean'))
# Production source inverse is exact: no declarations or options outside helper/call/three proofs change.
s=new.replace(helper,'').replace('  have hu := multiplier_units k₂ k₃ k₁₇\n','')
for p,e,term,proof in [(2,4,'1+8*k₂','hu.1'),(3,2,'1+3*k₃','hu.2.1'),(17,2,'8+17*k₁₇','hu.2.2')]:s=s.replace(f'convert value_scaled_unit {p} {e} ({term}) {proof} using 1',f'convert value_scaled_unit {p} {e} ({term}) (by omega) using 1')
assert s==old.read_text()
# Compare the helper formula/body with the actual independently completed scratch control.
scratch=w/'descent-evidence/progress-experiments/forward-actual-two-descent-root-divisor-orders-r16/scratch-small-prime-decidable/abstract_three_unit_control.lean.txt';txt=scratch.read_text();start=txt.index('lemma diagnostic_abstract_units');end=txt.index('\n\n\nrun_cmd',start);assert txt[start:end].replace('lemma diagnostic_abstract_units','private lemma multiplier_units')==helper[helper.index('private lemma'):].rstrip()
sys.path[:0]=[str(r/'scripts')];from check_lean import code_only
code=code_only(new);assert not any(t in code for t in ['sorry','admit','native_decide','axiom ','unsafe ','implemented_by','skipKernelTC'])
write(c/'STATIC_CHECKS.json',{'before_sha256':sha(old),'after_sha256':sha(c/old.name),'exact_inverse':True,'helper_formula_body_matches_completed_control':True,'public_statements_unchanged':True,'options_unchanged':True,'all_other_proofs_unchanged':True,'local_lean_run':False,'kernel_verified':False})
print('candidate',sha(c/old.name))
