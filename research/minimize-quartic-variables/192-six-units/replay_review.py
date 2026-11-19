"""Run the unmodified independent checker with its original relative file layout."""
from pathlib import Path
import subprocess,sys,tempfile,shutil
d=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as t:
 base=Path(t)/'lowvars-pub7';orig=base/'public/computation/quartic/seven_units193_v74/compact';new=base/'new192'
 orig.mkdir(parents=True);new.mkdir();shutil.copyfile(d/'brox193.quadratic-family.json',orig/'quadratic-family.json')
 for n in ['quadratic-family.json','certificate.json','polynomial-family.json']:shutil.copyfile(d/n,new/n)
 subprocess.run([sys.executable,'-B',d/'independent-original.py'],cwd=t,check=True)
