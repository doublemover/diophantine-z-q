"""Independent exact source-row checks; not a Lean proof or acceptance checker."""
from pathlib import Path
import re
import sys
import sympy as s

proof = Path(__file__).resolve().parents[3]
packet = proof / "experiments" / (sys.argv[1] if len(sys.argv) > 1 else "forward-three-detector-family-r1")
raw = (proof / "progress/Raw318FinalReplayData.lean").read_text()
literal = {int(i): v for i, v in re.findall(r"def r(\d+) .*? := (.*)", raw)}
rows = {i: s.sympify(re.sub(r"w (\d+)", r"w\1", v), locals={"S": s.Symbol("S")})
        for i, v in literal.items()}
v = lambda i: s.Symbol(f"w{i}")
c, t, z = s.symbols("c t z")
x, d = c**2*t, c**2*t-1
F = x*(x+s.Rational(1, 2))*(x+1)*(x-s.Rational(1, 2399))*(x+s.Rational(32, 407))
W = c**10*d**2/F
values = [x, x*x, x**3, x**3+s.Rational(3081901, 1205412)*x**4+s.Rational(976393, 602706)*x**5,
          -c*c*d, c**4*d**2, c**8*d**4, W*d**3, x*x-x**3/2, W, x*W*d**3,
          W**2*d**6, W**4*d**11, W**7*d**18, W**13*d**36, W**25*d**72]
for offset, first in [(0, 157), (1, 210)]:
    substitution = {v(194+51*offset+j): value for j, value in enumerate(values)}
    substitution.update({v(146): 1/t, v(145): z if offset == 0 else c, v(143): c-z})
    for j in range(16):
        assert s.factor(rows[first+j].subs(substitution, simultaneous=True)) == 0, first+j
for offset, first in [(0, 173), (1, 226)]:
    rename = {v(159+j): v(210+51*offset+j) for j in range(30)}
    rename.update({v(151): v(203+51*offset), v(156): v(207+51*offset), v(158): v(209+51*offset)})
    for j in range(30):
        assert s.expand(rows[120+j].xreplace(rename)-rows[first+j]) == 0, first+j
nonpole = list(range(152))+list(range(157, 205))+list(range(210, 258))
pole = list(range(152, 157))+list(range(205, 210))+list(range(258, 263))
written = set(range(39, 51)) | {191, 192, 193, 242, 243, 244, 293, 294, 295}
for i in nonpole:
    assert not written & set(map(int, re.findall(r"w (\d+)", literal[i]))), i
assert sorted(nonpole+pole) == list(range(263))
text = (packet / "ThreePoleCertificates318.lean").read_text()
terms = re.findall(r"(ha|hb)((?:\.[12])+)", text.split("theorem first263", 1)[1].split("exact ⟨", 1)[1])
def projection_index(path, length):
    bits = path.split(".")[1:]
    assert all(bit == "2" for bit in bits[:-1])
    return len(bits)-1 if bits[-1] == "1" else length-1
selected = []
for name, path in terms:
    source = nonpole if name == "ha" else pole
    selected.append(source[projection_index(path, len(source))])
assert selected == list(range(263))
for offset, first in [(0, 152), (1, 205), (2, 258)]:
    rename = {v(39+i): v(39+4*offset+i) for i in range(4)}
    rename.update({v(190+i): v(190+51*offset+i) for i in range(4)})
    for j in range(5):
        assert s.expand(rows[152+j].xreplace(rename)-rows[first+j]) == 0
print("PASS:32 weight equations,60 chain relabelings,15 pole relabelings,263 exact row projections,21-coordinate preservation")
