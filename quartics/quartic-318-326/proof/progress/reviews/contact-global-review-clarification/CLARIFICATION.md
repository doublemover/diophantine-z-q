# Scope correction to the contact-global source review

The first section of `contact-global-review/REVIEW.md` contains the sentence
"Normality of the entire source is derived from the actual finite étale domain
over the normal localized polynomial base, rather than supplied for a selected
component."

Here "entire source" must be read as **the entire source open**,
`ContactKummerOrder318.OpenOrder c`. The exact checked endpoint
`SourceNormalChart318.source_integrallyClosed` has that type. It does not prove
normality of the unlocalized `ContactKummerOrder318.SourceOrder c`. The preceding
review sentence distinguishes that localization, but this sentence's wording
was too broad and is corrected here without editing the frozen review.

The original whole order's specified fraction field, the normality of its
entire source open, the global normalization's finiteness/properness and
regular stalks, and the actual infinity open immersion remain accepted at
the previously stated scope. Whole unlocalized source normality requires the
four-branch-open descent now being developed separately. This clarification
is not evidence that the later descent already passed, and is not a fresh
kernel replay or manuscript incorporation claim.
