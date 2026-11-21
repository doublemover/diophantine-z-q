#!/bin/sh
set -eu
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
(
  cd rc-linked-four-pole-common-q-r1
  sha256sum -c SHA256SUMS
  python3 -B check_scalar_same_q_prefix.py | cmp - ACTUAL-COMMON-Q-SCALAR-PREFIX.json
)
(
  cd common-fixed-q-cold-r1
  sha256sum -c SHA256SUMS
  python3 -B check_common_fixed_q_independent.py ../rc-linked-four-pole-common-q-r1/ACTUAL-COMMON-Q-SCALAR-PREFIX.json | cmp - INDEPENDENT-COMMON-Q.txt
)
check () {
  (
    cd "$1"
    sha256sum -c SHA256SUMS
    python3 -B "$2" | cmp - "$3"
  )
}
check linked-detector-fixed-scalar-prefix-r1 check_explicit_labels.py EXACT-LABEL-GUARD-CONTROLS.json
check linked-detector-fixed-index-necessary-r1 check_contact_leading.py EXACT-CONTACT-LEADING-CONTROLS.json
check linked-detector-fixed-index-genus-five-r1 check_contact_genus_five.py EXACT-FIVE-CONTACT-QUOTIENTS.json
check linked-detector-finite-saturation-r1 check_contact_escape.py EXACT-FINITE-CONTACT-ESCAPE-CONTROLS.json
check linked-detector-finite-saturation-plus5-r1 check_contact_two_form_plus5.py EXACT-CONTACT-TWO-FORM-PLUS5.json
check linked-detector-known16-exhaustion-r1 check_fixed_h_known16.py EXACT-KNOWN16-EXHAUSTION.json
check joined-slot190-known16-cold-r1 check_known16_residues.py INDEPENDENT-STATUS-ROWS.txt
printf '%s\n' 'All exact scalar, local, genus, and independent finite replays matched.'
