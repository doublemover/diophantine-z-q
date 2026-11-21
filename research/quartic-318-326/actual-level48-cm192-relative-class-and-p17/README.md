# The next marked trace sign and the CM intersection at 17

The next marking sign of the rational quarter is an oriented intersection calculation at level 48, with a fixed CM fibre of discriminant −192. For the first arm of the allowed balanced pair one can refine the shared final prime to force an actual simple intersection at 17. Nevertheless the integral order of the total signed ideal is even at each place over 17, on either arm. These are separate results; the one nearly transverse collision does not certify odd parity.

The remaining sign can be read from a relative ideal-class relation over the fixed real quartic field \(\mathbb Q(\sqrt3,\sqrt{17})\). The actual signed ideal, the final residue sign, and the selected curves' ranks are not computed.

- [Cyclic-four trace and fixed CM fibre](marked-cyclic-four/ACTUAL-LEVEL48-MARKED-CYCLIC-FOUR-CM192.md)
- [Admissible actual collision and its multiplicity](actual-intersection/ACTUAL-CM192-LEVEL-INTERSECTION-AT-17.md)
- [Relative class-sign criterion and evenness at 17](relative-class/ACTUAL-CM192-RELATIVE-CLASS-SIGN.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-RELATIVE-CLASS-AND-P17-REVIEW.md)

The finite certificates verify the marked discriminant and level tower, and the conductor-16 ray and lattice arithmetic. They do not evaluate a full CM orbit.

    (cd marked-cyclic-four && python3 -B replay_marked_cyclic_four_cm192.py | cmp - EXACT-MARKED-FIBRE-CM192.json)
    (cd actual-intersection && python3 -B replay_cm192_level16_ray.py | cmp - EXACT-CM192-LEVEL16-RAY.json)
    sha256sum -c SHA256SUMS
