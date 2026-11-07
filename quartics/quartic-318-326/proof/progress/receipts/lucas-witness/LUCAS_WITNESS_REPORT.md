# Literal Lucas witnesses

Status: proved with Lean's kernel. LucasWitness318 contains six public theorems and 21 recursively audited declarations, with only the standard axioms propext, Classical.choice and Quot.sound.

- `U_norm` proves the exact consecutive-term norm identity.
- `positive_witness_at_index` constructs positive integral t,z whenever the positive index k is divisible by |s−2|. It retains the exact formulas t=U_|s|(k+1) and |s−2|z=U_|s|(k).
- `positive_witness` proves positive integral existence for every |s|≥3, including negative s.
- `U_mod_two` proves the actual period 0,1,1 for odd parameters.
- `positive_odd_witness_at_index` constructs positive odd witnesses when additionally k≡1 modulo three and s is odd.
- `source_positive_odd_witness` specializes to the exact completeness choice k=2(s−2), for positive odd s≥3 with s≡1 modulo three.

The construction supplies the literal equation t²−s(s−2)tz+(s−2)²z²=1. It does not assert prime-pattern existence, restricted-converse norm certificates, CRT point realization or all final source constraints.

Replay: `./check_global.sh LucasWitness318 && ./check_global.sh LucasWitnessAudit318`. Audit output: lucas-witness-audit.log. The already frozen Lucas-growth modules are unchanged.
