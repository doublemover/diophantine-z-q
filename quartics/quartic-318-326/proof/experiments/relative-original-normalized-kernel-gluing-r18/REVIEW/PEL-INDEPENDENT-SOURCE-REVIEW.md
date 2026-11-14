# Independent source review of Picard repairs

Reviewer: sibling PEL repair agent, distinct from Picard author. This is source-level candidate acceptance only, not Lean acceptance. No local compiler ran.

Compared all three exact before/after pairs and the actual run 43611323966 ContactCoefficientRestrictionSquares318 log. The unit normalization proof replaces ac_rfl with two ordinary commutative group laws: reverse-order inverse factors are swapped under multiplication by z*w, then mul_mul_mul_comm interleaves the factors. Same coefficient, lift, normalization map and full arbitrary-unit domain.

The wholeSection helper keeps the native underlying whole section and forgets only the affine scalar interpretation. Its identity term and injectivity term explicitly require definitional identity of those carriers; this is not a new injectivity assumption. The two consumers apply that injection to the exact overlap pullback object over S, then compare the existing original_square result. Both finite and distinct infinity charts, full arbitrary sections and original pullback maps remain. Removing moduleSpecΓFunctor/modulesSpecToSheaf from simplification avoids unnecessarily expanding the concrete carrier; the new wholeSection unfolding instead exposes the original geometric target.

The authentic error contrasts the geometric top-section equality with the expanded affine scalar wrapper. The proposed bridge targets that mismatch without a new mathematical hypothesis. Hosted checking must still establish helper definitional equality, exact elaboration of both consumer applications, and final simp closure. Existing resource and transparency options are unchanged. No complete gluing, packet or arithmetic theorem acceptance follows.

## Exact bindings
- DualUnitFactorization318: before 6199358cd87d2a4947db1175a8c39548117f85f955b16b445a8bcd15176a2373; after fe4765c352620ae4d5dbcf406f4e8e61dee598bf5e698b4cc7340fabbf930aec.
- OriginalAffinePathWholeSections318: before 59b582ee6d4957958429936fc259b08e1b62c04c1d57e88336b689cd01e15992; after 7decc03906f4734b7481b9e2c538c3da575e29b8e0383d5dbf6a976cc84b33ca.
- ContactCoefficientRestrictionSquares318: before 3d46e39faea16541608a7bc9d9480722f0c8dd47c2f9a1382bdda0aee1aa4e84; after 91c04714bf1e14f1287b763ba4054fe1ddeb4ab02fddf58158cd553b54e28d12.
