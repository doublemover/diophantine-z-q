# Actual holomorphic chart energy transport

This packet supplies the ordinary local area-energy hypothesis of the actual Wronskian theorem from exact holomorphic change of variables and a normalized global energy measure. The functions, derivatives, real determinant, Lebesgue integrals, image sets and measure pushforwards are actual Mathlib objects. No local coefficient estimate, Jacobian estimate, local energy bound or final Wronskian bound is assumed.

## Checked interfaces

`HolomorphicEnergy318.complex_jacobian` proves that the real determinant of multiplication by a complex number a is exactly norm(a)^2. `real_derivative` binds this to the actual complex derivative of F.

For an injective holomorphic map F on an open set s, `integral_pullback` proves

    integral_s |f(F(z)) F'(z)|^2 dA
      = integral_(F(s)) |f(w)|^2 dA.

`integrable_pullback_iff` gives the corresponding genuine integrability equivalence. These use Mathlib's real finite-dimensional Jacobian theorem, not an asserted complex change-of-variables law. No lower bound or nonzero-derivative premise is added. Injectivity is essential to avoid multiplicities. The ordinary-area normalization has no extra factor two.

`pullback_energy_le` and `pullback_energy_one` derive integrability and the local energy bound from integrability on a larger region containing F(s) and its global energy bound. The Jacobian is retained in the actual pulled-back differential coefficient.

`GlobalEnergyMeasure318` handles a genuinely non-planar ambient measurable space X. Given a global energy measure mu of mass at most one, a chart region U, coordinate q, and the exact identity

    map(q, mu restricted to U)
      = (ordinary area restricted to t) with density |f|^2,

`chart_energy_mass` proves that the local energy is exactly mu(U). `normalized_chart_energy` derives local integrability and energy at most one from the global mass, using only measurability of the coordinate coefficient. The density identity is not a local bound. `normalized_pullback_energy` also allows a further injective holomorphic chart transition.

`ChartWronskian318.pullback` is the actual coefficient f(F(z))F'(z). Holomorphicity is proved from the complex differentiability of F and f, including the differentiability of F'. `coefficient_from_global_energy` composes to the sharp factorial-normalized coefficient bound. `wronskian_from_global_energy` composes to the actual factorial Wronskian bound.

The strongest final theorem, `wronskian_from_global_measure`, starts with one normalized global energy measure per differential, their exact chart density identities, a common injective holomorphic chart and actual holomorphic coefficient functions. It derives all local integrability and energy inputs and concludes

    log |Wr_q| <= 100 g^2 log(2 g N),

under g>=1, N>=1 and radius>=exp(-21)/N. Its proof does not receive a local energy inequality or integrability premise. Actual derivative and determinant normalizations are preserved end to end.

## Geometric boundary

The packet does not invent or assume a Lean Riemann-surface model. Producing the actual global differential-energy measures from the compact curve, proving their normalization by the global (i/2) pairing, and proving their coordinate-density identities remain explicit geometric inputs. For a holomorphic differential omega=f(z)dz, the standard identity (i/2) omega wedge conjugate(omega)=|f(z)|^2 dx dy is the interpretation of that density. The actual holomorphic coordinate-transition and measure restriction steps are now checked here.

The `mu` measures are ordinary nonnegative measures. Their mass may be less than one; equality one is stronger than needed. The density equation is precisely what excludes a missing covering multiplicity or incorrect coordinate measure. No statement that the entire `FiveContact49Height` theorem is formalized follows from this packet.

## Reproduction

Run `bash build-all.sh`. It uses the installed Lean4.35 toolchain and the frozen `wronskian-local/frozen` packet, with `debug.skipKernelTC=false`. The audit traverses every declaration in all three modules, including generated/private declarations, and recursively permits only propext, Classical.choice and Quot.sound. The receipt records accepted inputs and outputs. No repository or other worker's files were modified.
