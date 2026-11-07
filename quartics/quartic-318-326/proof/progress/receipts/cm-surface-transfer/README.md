# Exact CM surface-to-contact transfer

Three public Lean theorems, kernel checked, standard axioms only.

V10's inherited854R estimate bounds the stable Faltings height of the CM abelian surface A. It does not directly bound the rational contact height. `actual_CM_contact_bound` composes that actual surface estimate with h(contact)<=2h(A)+120, and proves the required cap 2^68*C²*R^(49/8)+128. The intermediate bound is1708R+120.

`surface_normalization_bound` checks the exact dimension-two shift h_shifted=h_original+log(pi)<h_original+2. `actual_CM_shifted_contact_bound` proves the same final cap even when this shift is inserted explicitly before the geometric comparison.

The older frozen `IsogenyHeightTransfer318.contact_height_CM` is a valid generic domination lemma for its stated premise hContact<=854R, but that premise should not be described as V10's direct CM theorem. The present packet supplies the exact source-facing application, without modifying the frozen theorem or its hashes. No checked endpoint depended on silently asserting the stronger premise.

The actual upstream CM854R arithmetic/geometric producer is separately being validated. These finite transfer lemmas do not prove it or FiveContact49Height.

Replay: ./build.sh, with -Ddebug.skipKernelTC=false.
