# Independent actual Weierstrass ODE and global injectivity review

Accepted. Exact copies of all five mathematical source modules were rebuilt in dependency order with the copied directory first in LEAN_PATH. A combined exhaustive audit passes all17 declarations, with only propext, Classical.choice and Quot.sound. The original frozen source hashes are unchanged.

The second-order equation is correctly proved even where wp' vanishes. Differentiating the actual cubic gives wp' times the ODE defect equal to zero on the complement of the lattice. Analytic product uniqueness on that connected set forces one factor identically zero. The actual order−3 pole excludes the wp' factor, so the ODE defect is identically zero. No division by a potentially zero wp' is used. The actual modular discriminant then excludes simultaneous zero coordinate derivatives and gives local pair injectivity by the genuine analytic inverse theorem.

The analytic germ uniqueness theorem has the necessary neighborhood ODE hypotheses, not just an identity at one point. Strong induction and the Leibniz formula determine all derivatives from the common initial value/first derivative; the analytic-order theorem gives equality on a neighborhood.

Applying that result to wp(z) and wp(z+d) is valid wherever both arguments avoid the lattice. The complement of the union of the lattice and its translate is connected: these are countable subsets of the real plane, and the actual connected-complement theorem applies. Analytic continuation gives equality throughout that complement. If d were not a lattice point, the translated function would be continuous at0; equality on a punctured neighborhood would contradict the actual order−2 pole of wp. Thus the actual pair separates points modulo the actual lattice, without any supplied finite-fiber or global injectivity theorem.

The final point-level proof handles the infinity branch separately and cancels only the nonzero explicit powers of2*pi in the affine normalization. Quotient equality uses the actual additive lattice relation. Its conclusion is genuine injectivity of the actual torusPoint function.

This review does not infer surjectivity, addition compatibility, a global analytic isomorphism or the specified modular-fiber identification. Later packets may establish those separately; they are not prerequisites covertly assumed here.
