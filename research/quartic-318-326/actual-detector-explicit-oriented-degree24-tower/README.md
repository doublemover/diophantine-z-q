# Explicit field tower for the one-companion 5-class criterion

The exact proof writes the moving degree-24 field as a degree-six line field followed by two quadratic steps, and gives the automorphism that acts by scalar 2 on the chosen covector. It extends the [published sufficient class-group criterion](https://github.com/doublemover/diophantine-z-q/tree/8a20b6a4f42d9293c434c50dbcf24430417b78a9/research/quartic-318-326/actual-detector-moving-degree24-five-class-gate) without constructing a degree-480 division field. It does not give a selected numerical twist, computed class dimension, rank, or point.

Verify all bytes and replay the rational coefficient identities and two fixed Frobenius controls with Python's standard library:

```sh
sha256sum -c SHA256SUMS
(cd author && sha256sum -c SHA256SUMS &&
  python3 -B replay_explicit_tower.py | cmp - EXACT-EXPLICIT-TOWER-CONTROLS.json)
(cd cold && sha256sum -c SHA256SUMS)
```
