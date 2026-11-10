# Independent source review: forward local norm/quadric counts243

Reviewer: resume_pel_order. Producer: resume_integer_arithmetic. Date:2026-11-10.
Frozen APPLICATION SHA-256:
43ca323863d3f8a692ceafc78cc0d835f4290282a16eb8fea0872de85aeeb5ae.
All243 source hashes checked; all239 forward-jacobi-cm-producer-r1 sources
byte-identical. No candidate file changed.

Disposition: four-source finite-count delta source-reviewed in its stated odd-
characteristic/nonzero-kappa scope. No Lean/kernel acceptance or analytic prime-
pattern, rational twist realization or global Anchor conclusion.

Read all four new sources in full. FiniteDifferenceConic318 uses the actual
invertible change (x,y)↦(x-y,x+y), with explicit 2≠0, followed by the nonzero
product fiber equivalence to F-units, with explicit t≠0. The alternate sigma
partition counts all ordinate fibers including zeros. Thus sum chi(x²-t)=-1
is derived for t≠0; no zero-t use slips through the Gaussian norm argument.

FiniteGaussianNormCount318 treats norm0 separately and retains the actual origin.
The square-character sum removes precisely x=0, where chi=0, and is q-1 on
nonzero x. Consequently N(0)=q+(q-1)chi(-1) and N(t)=q-chi(-1) for t≠0, valid
in both split and inert cases. No chi(-1)=1 specialization is silently used.

FiniteNormDifferenceCount318 partitions the literal four-coordinate fiber by
its first actual norm t, with second norm t-s. In the indicator convolution,
t=0 and t=s are each included, and the overlap contributes B² ONLY at s=0.
Using chi(-1)²=1 gives q³-q+q² when s=0 and q³-q otherwise. The zero-difference
correction is present and survives into the five-variable count.

FiniteFiveQuadricCount318 partitions the same five original coordinates by w.
The explicit kappa≠0 hypothesis makes kappa*w²=0 equivalent to w=0. Therefore
exactly one fiber gets the q² correction, giving q⁴ in every nonzero-kappa
case. The final subtype removes exactly one actual zero vector, giving q⁴-1.
Here “primitive local” means nonzero over the residue field; no unproved
integral/adically primitive lifting theorem is claimed.

Independent exhaustive finite computations for q=3,5,7,11,13 checked every
Gaussian norm value, every four-coordinate norm difference, every nonzero-kappa
five-coordinate count and every nonzero-t character sum, including both signs
of chi(-1). These support source review but do not certify the general Lean
proof. All theorem assumptions are explicit or occur in theorem result types;
no omitted proof-only section hypothesis was found.
