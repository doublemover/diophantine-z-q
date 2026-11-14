# Observed chosen-pole normalization annotation repair

Run43586414080, headf89bd0a3cb8a788d6c7f2f494a21d7d103a893cb. Source-only candidate, not kernel acceptance. Exact zero and cotangent artifacts show preceding ComplexSphereAffineAutomorphisms318 exit0, then this module fails solely at two ambiguous infinity expressions and the resulting coe-branch cascade.

## 1. Required inputs
For every p:OnePoint ℂ, poleCoordinate p is the existing genuine homeomorphism of OnePoint ℂ. Its evaluation theorem must land at the OnePoint infinity, not ℕ∞ω. The pinned imported OnePoint.Basic definition and scoped notation are the native source. Only those two endpoints receive explicit `(∞:OnePoint ℂ)` annotations.

## 2. Constructed objects
poleCoordinate is unchanged: at infinity it is Homeomorph.refl; at finite z it is affineSphere 1 (-z) one_ne_zero followed by inversionHomeomorph. The existing sphereCharts and IsManifold structure, and all inherited affine/inversion aliases, stay identical. No substitute coordinate or transported topology is constructed.

## 3. Complete domain coverage
The theorem keeps every p:OnePoint ℂ and both branches of the same OnePoint.rec induction. At infinity the proof remains rfl. At finite z the exact existing cancellation 1*z+(-z)=0 followed by inversion_zero remains. No finite pole, zero, infinity or branch is excluded.

## 4. Maps and directions
The affine translation sends the selected finite pole z to zero; the original inversion then sends zero to infinity. The existing trans composition, coordinates, inverse and holomorphy proof are untouched. The annotations only disambiguate the codomain point in the theorem and its finite-branch change target.

## 5. Identity consumed
The actual object remains poleCoordinate p and its equation poleCoordinate p p=infinity. It is not an existentially chosen equivalent map. The published FourPoint and projective-line consumers require exactly this homeomorphism/evaluation, and no geometric equality is assumed in place of deriving it.

## 6. Exact consumers
ComplexSphereFourPointNormalization318.pole_finite rewrites poleCoordinate_at at line15; normalization_zero uses it at line48; its holomorphy proof uses poleCoordinate_holomorphic at line82. ProjectiveLineFourPointAlgebraicNormalization318.pole at lines47-51 realizes this exact poleCoordinate by identity or the same affine/inversion composition, and fourPoints composes that realization. The latter consumes the coordinate definition, not a fabricated direct use of poleCoordinate_at. Copies are evidence only and remain unmodified.

## 7. Coefficients and exceptional points
The field remains ℂ, the translation coefficient remains1 with unchanged one_ne_zero, and translation remains -z. Composition order and inversion_zero sign/point convention are unchanged. Both finite and infinite chosen poles are covered, with no nonzero or distinct-point premise added to this theorem.

## 8. Literal statements and assumptions
The public theorem's literal text gains a OnePoint type annotation, repairing an ambiguous failed statement; byte-identical statement text is not claimed. Its intended quantified input and conclusion stay the same. The second change is the matching proof-local target annotation. All definitions, imports, other proof text, typeclass instances and resource/trust options remain byte-identical. No admission, axiom, diagnostic setting or weakened conclusion is introduced.

## 9. Evidence and acceptance boundary
Each own RESULT pins its actual published predecessor intake; source before bytes match both packets. Artifact metadata/run/head/digest and actual ZIP logs are retained separately. The prior producer's module exit0 is observed, but this candidate has not run in Lean. Independent source/contract review, exact propagation review, hosted full-module checking and final packet audits remain required. No complete packet or arithmetic theorem acceptance is claimed. Geometry diagnostics belong to another run and are not this candidate's evidence.
