# Local regularity audit

`BuresLocalRegularity.lean` proves that preservation of the literal Bures
distance makes a map of the positive-definite cone a continuous topological
embedding in the ordinary matrix topology. This is the exact `C⁰` conclusion
from the current metric API, and is not a smoothness theorem.

`BuresSquareDerivative.lean` proves that squaring a complex matrix has
Fréchet derivative `H ↦ S*H + H*S`. The existing `Sylvester.lean` gives
bijection of this linear derivative when `S` is positive definite. These are
two substantive ingredients for differentiating the positive matrix square
root using `HasFDerivAt.of_local_left_inverse` from
`Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`.

The direct argument on the full complex matrix space does **not** apply to
the project's `matrixSqrt`. Positive-definite Hermitian matrices have empty
interior in the complex matrix space; the proved CFC continuity in
`BuresTopology.lean` is continuity restricted to the semidefinite/Hermitian
subtype. `HasFDerivAt.of_local_left_inverse` instead needs continuity at a
point in an open neighborhood in its domain. The CFC square root has not been
shown continuous as a function of arbitrary complex matrices near a positive
Hermitian matrix.

The viable next type is the real normed space of Hermitian matrices, e.g.
`selfAdjoint (Mat n)` with its real `StarModule` structure. One must:

1. establish its real Banach-space instance and that positive definiteness
   is open in this space;
2. restrict squaring and its Sylvester derivative to Hermitian matrices,
   making the latter a continuous real linear equivalence (the Hermitian
   uniqueness theorem in `Sylvester.lean` supplies bijectivity);
3. show the actual CFC square root, restricted to this open positive cone,
   is continuous and is a left inverse of squaring;
4. apply `HasFDerivAt.of_local_left_inverse` for a real derivative of the
   square root, then differentiate the literal fidelity and prove that nearby
   squared-distance coordinate functions have an invertible Jacobian.

The last Jacobian theorem is necessary for the distance-coordinate proof of
smoothness: for `n²` anchors near each point, the values of squared distance
to the anchors should form a local coordinate chart. The isometry preserves
these values; composing with the destination chart inverse would make it
smooth. No such coordinate chart is currently formalized, nor did a bounded
search of the pinned mathlib find a CFC square-root derivative theorem or a
Myers–Steenrod substitute. These are proof obligations, not assumptions in
the existing compiled theorem.
