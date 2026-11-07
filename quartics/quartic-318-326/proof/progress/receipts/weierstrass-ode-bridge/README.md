# Actual Weierstrass second derivative and local pair injectivity

Strict kernel replay and exhaustive recursive audit: PASS9 declarations in2 modules, standard axioms only. All9 declarations are public proved lemmas/theorems.

WeierstrassODE318 proves the actual derivative has order−3 at the origin and cannot vanish identically off the lattice. Differentiating the actual cubic identity gives the product of the first derivative and the second-order residual. Analytic product uniqueness on the connected lattice complement removes the first factor, including its zeros, and proves ℘''=6℘²−g₂/2 everywhere off the lattice. No ODE or nonvanishing-derivative hypothesis is supplied.

WeierstrassImmersion318 computes g₂³−27g₃²=4096π¹²Δ using the actual modular discriminant, which is nonzero. The two actual coordinate derivatives therefore cannot vanish together. The analytic inverse-function theorem on a coordinate proves that (℘,℘') is locally injective near each non-lattice point.

This is local injectivity, not global injectivity modulo the lattice, surjectivity, an additive torus map, or uniformization. The global pair-injectivity and global curve identification obligations remain explicit.

Run bash run.sh. Accepted modules are WeierstrassODE318 and WeierstrassImmersion318; Check.lean is only a diagnostic and is excluded.
