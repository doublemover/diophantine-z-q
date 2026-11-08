# Actual Scheme-test cancellation for the literal family

Three modules, 92 declarations, fresh strict Lean checks and recursive axiom audit passed. The required final endpoints are explicitly checked for existence. Only propext, Classical.choice and Quot.sound occur recursively. Hosted joined integration and independent source/application review remain pending.

The main theorem is `LiteralSchemeCancellation318.tripling_zero_iff`: for every Scheme T and actual map t into the completed literal curve, the actual tripling composite is the zero section over t's structural map if and only if the actual doubling composite is global negation. No affine, field or reducedness condition is imposed on T. All natural levels N are allowed.

The maps are the frozen completed addition, actual infinity section, global negation and actual pullback lifts. This is a cancellation theorem for the literal family, not a general-coefficient associativity assertion or a complete tripling-kernel identification. In particular, finite nonverticality and the global zero-section decomposition remain separate obligations.

The check used the shared compiler lock and existing predecessor objects. No full chain was replayed in the cloud, and the shared repository was not modified. See APPLICATION.md for the exact comparison and dependency scope.
