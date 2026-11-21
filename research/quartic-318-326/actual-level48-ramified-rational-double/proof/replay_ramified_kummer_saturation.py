#!/usr/bin/env python3
from itertools import product
import json
# Columns are T_0, T_{-1}, M. Rows are the two nontoy support types.
columns = ((1,1,1,1), (1,0,1,0), (0,0,1,0))
mat = list(map(list,zip(*columns)))
def image(c):
    return [sum(x*y for x,y in zip(c,row))%2 for row in mat]
rows = [{"coefficients":list(c),"parities_q0_and_genuine_beta_prime":image(c)}
        for c in product((0,1),repeat=3)]
assert len({tuple(x["parities_q0_and_genuine_beta_prime"]) for x in rows})==8
assert [x["coefficients"] for x in rows if not any(x["parities_q0_and_genuine_beta_prime"])] == [[0,0,0]]
print(json.dumps({"matrix":mat,"checked_all_selected_selmer_parity_rows":rows,
    "scope":"Literal parity table, no evaluated phase or actual point."},sort_keys=True,indent=2))
