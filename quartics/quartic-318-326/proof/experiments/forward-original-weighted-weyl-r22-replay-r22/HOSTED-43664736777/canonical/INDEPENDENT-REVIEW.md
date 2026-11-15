# Actual two/three-adic preparation source review

PASS for exact source/application review and future scoped propagation, not Lean acceptance.

Candidate395d63297b75703edc6f7f08fafcd99ea0b2b3a868edc81605639aa32da3b944. Manifest2d30f473cf6df1a09bec680969decc685266b58d5fa71e346c66b37784c522ac; all13 bindings independently verified. Read entire source, exact diff, current errors and nine-clause application.

Eight rewrites now explicitly expose the same local witness abbreviation w before applying detector33/detector37. This preserves the actual full witness, gate values and norm/half-trace expressions rather than replacing them. The additional typed hself : padicValRat 2 (2:ℚ)=1 uses native padicValRat.self(p:=2) and the same Nat.cast_ofNat normalization already validated in the preceding HalfTrace module. It removes ambiguity in the original product rewrite without changing any valuation equation or Fact instance.

All integer a/h/labels, h≠0, labels1≠0,1, exact offset15/depth, three-adic parity and strict-depth conditions, inputR orders and final actual_unit consumer remain unchanged. No positivity, stronger local premise, selected case or adjusted denominator is introduced. Public types, imports and options are unchanged.

Both own run43664736777 receipts/intakes are bound. Descent21 RESULT5dd9d91ab94ecb1d938f0ea2c3bf26735a8440b4eab8a8df73e5e142c6fdb216 and weighted21 RESULT19d18f95591c2924755c52a711ca9cb400df20e3d81343f97534bcbd821f0509 have105 full-module passes, including HalfTrace2.019s/1.669s, then TwoThree failure2.170s/1.671s. The eight hidden-w rewrites and untyped prime-self rewrite are the observed surfaces. Candidate still requires hosted Lean; no local Lean or full closure acceptance is claimed.
