# FiveContact49Height realization boundary

Audit basis: branch add-quartic-318-326 at 5e483a2 before these experimental additions. The accepted progress sources remain unchanged. This inventory distinguishes a proved conditional implication from existence of its inputs.

## Exact endpoint

ContactHeight318.FiveContact49Height quantifies over every primitive pair of integers u,v for which the literal five forms are nonzero. Its support is the fixed bad-prime product multiplied by the **odd-contact** radical. It is not the full radical of the five values. An ordinary abc bound for the full radical does not directly discharge this interface.

FiveContactProducer318.five_contact_of_realization proves the bound from GeometricRealization. RefinedContactRealization318.five_contact_of_refined_realization proves it from RefinedGeometricRealization. Neither global realization is asserted. The refined theorem produces the contact-to-surface inequality from local section norms instead of retaining that inequality as a field.

## What the new producer advances

A genuine field-valued point of the original contact model is now constructed in the proposed RationalContactPoint318 source for every rational coordinate, with a degree-at-most-sixteen number field and an exact modelMap square. The historical fiber/model packet already gave a classical existence route; this is a new formal producer for one of its concrete curve-level steps, not a new mathematical discovery or proof of its PEL interpretation.

The new field is not automatically any of the separate fields quantified by the refined endpoint. In particular it does not replace the full marking/splitting field of degree at most 576, the non-CM isogeny field of degree at most 2304 times support, the semistable model/averaging field, or the integral-section field.

## MetricSections still requires a geometric source

RefinedContactRealization318.MetricSections contains two field elements with ratio 32u/v, nonzero a0, canonical and Hodge FrameNorms, an actual all-place image-lattice equality, and finite/archimedean bounds. SectionHeight318.FrameNorms is a record of positive local real numbers with finite support; the record alone does not construct a line bundle or identify it with a Hodge determinant.

The actual global intrinsic bicanonical sections and their full-chart relations are constructed in ContactGlobalBicanonical318 and ContactBicanonicalSectionRatios318. Remaining integration must:

- evaluate those same sections at the actual chosen arithmetic point and compare the frame with the maximal-stack canonical line;
- construct the integral extension and prove the finite-place inequalities for the same scaled sections;
- identify the archimedean norms with the already bounded hyperbolic/Petersson metric;
- construct the actual universal surface/Hodge determinant and prove the all-place KS image equality with factor 210.

The historical maximal-ks-producer/MAXIMAL-KS-PRODUCER.md sections 2–5 supply a classical theorem application. It explicitly uses the maximal stack, forgets the level marking without changing the surface, and pulls back the maximal canonical line. It does not replace that line by the level-three dualizing line. The checked induced-lattice and degree calculations consume, rather than construct, this identification. The original surface height differs from the Yuan height by log(pi); this shift remains different in the CM and non-CM records.

## CM branch

CMInputs still needs an actual CM fiber surface, its same-field maximal-order elliptic factor, fundamental discriminant with the specified support, reduced periods and the Silverman height identity, the product-height identity, and a controlled isogeny with its degree and height variation. The checked eta bound and finite logarithmic arithmetic then apply. The earlier cm-height-producer/CM-PRODUCER.md provides the classical same-field argument and explicitly does not define abelian varieties or their heights in Lean.

## Non-CM branch

NonCMInputs needs the actual modular/quotient component attached to the surface, level/index/conductor bounds, genus data and a selected non-Weierstrass fiber. Its CuspArakelovData318.Data fields quantify over every embedding of the actual averaging field and contain a normalized modular function, cusp width and period, and a full genus-indexed family of differential functions with energy and Wronskian conditions. Existing analytic modules prove substantial actual j/cusp and coefficient facts, but no blanket construction of this complete record is supplied by their existence alone.

SourceJacobianBound318.FiniteData contains an exceptional intersection matrix, its negative-definiteness and off-diagonal signs, local divisor coefficients, adjunction and the section projection inequality. The arithmetic model, full component indexing and identification of those matrices/coefficient arrays with that model remain to be produced together.

SourceNonCMHeight318.ArakelovIdentifications contains the minimal-model intersection inequality, the Faltings–Wronskian inequality and the GR normalization. These are explicit source applications, not consequences of naming unrelated real numbers hFal and hGR. The quotient image-height comparison, controlled isogeny field and isogeny variation must apply to the same actual surface.

## Historical disposition and verification

The earlier fiber-field, maximal-KS, CM-height and source-Arakelov application arguments are retained as classical/source-level evidence. They are not newly disproved by the absence of Lean objects. Their incorporation into unconditional Lean data existence remains pending. A successful compile or recursive axiom audit of this three-module packet would certify only its stated curve-level field/point construction, not these global realizations or the final arithmetic theorem.
