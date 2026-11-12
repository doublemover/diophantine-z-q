# Hosted a1735 early cast repair

The inherited native-Pontryagin run stopped at UniformScaledPoleDomain318.lean:76, before the new arithmetic modules, because exact_mod_cast retained projections of the rewritten real pair. The successor adds exactly `simp only [Prod.fst, Prod.snd] at hb` immediately before the same exact_mod_cast. The source and theorem statement are otherwise byte-identical. No global arithmetic result or hosted success is inferred. The predecessor failed packet is preserved unchanged.
