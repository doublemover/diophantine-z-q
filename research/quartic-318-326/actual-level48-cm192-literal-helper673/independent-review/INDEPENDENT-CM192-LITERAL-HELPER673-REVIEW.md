# Independent exact review: literal helper 673 local cell

Signed: Vesper, independent mathematical reviewer, 2026-11-21. Disposition: PASS for the fixed local cell, not a global witness.

Author SHA256SUMS 14805d48f46d8ea00ed24f9141efd120cc9b3373bfcb653d3af8b2950126e012; paper b4ae691e04eeadf45aa59dcf531d7bd7aa1c2d175b65dc3284fba799004ee43e. All exact author checksum entries and the standalone replay byte comparison passed. The pinned actual a=0 original scalar/label input 5a70adc6e54b42f7d5d289b00a3e0311b7a938e39c489e7a2c3e3781736e2be7 matched its published original scalar-prefix bytes. Its old q=1041427 is not the unchosen new linear-key denominator prime.

I found all five exact source blobs in the published source and independently compared the 21 actual gate definitions and the sixteen signed/nonsquared literal leaf positions:
- DetectorGateWitness318, 5c6c61539543b60806bada94c2af35681ef98796d38e795c05ea74cb081a724d.
- CoherentMultipleCharts318, 01443a070ea295862a1c06111e8803651d6766afead3c3918797aa5718ba9bc9.
- CoherentMultiplePrefix318, 54c2bffb492db9c8f7ae7ec30a3c6d6f7bab17de617f3f90a5b9a2ac2a63ba46.
- ActualPadeRatios318, 536503bb576c233ab948145db9d323ea5f28b5c96bacb6b1953fced45ea74244.
- ActualDetectorFold318, 1bb3b85f8bc3ca7bd58c252ebda8b416b7011905a212a6aae7ec9c1ee5513cf5.

Independently of the author's paired-coordinate fold I iterated both separate split field embeddings, then recovered the trace quotient and all three poles. At I=673 and t=61, their pole/companion pairs are (628,162), (84,194), (472,92); each is regular and of unit pole value. The slot-190 companion is the nonzero square 145 squared. The two actual source curve orders are each exactly 314, independently checked by annihilation at 314 and nonannihilation at 2 and 157; the fixed index reduces to 290 on both. I checked both independent residue signs at 17 and q*=5, and the five contact-form norms in the first row were all nonzero squares. The comparison uses the actual scalar anchor and only the stated local index class.

This verifies an admissible row-specific local cell before any new linear key. It does not construct a new rational key, the final shared integer index, the actual selected discriminant or Hecke product, a nonzero mark, a rational point, or a rank.
