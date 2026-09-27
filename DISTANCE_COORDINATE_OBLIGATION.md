# Distance coordinates: exact remaining regularity obligation

`BuresSquaredSmooth.lean` now proves that the literal squared Bures distance
`distance A B ^ 2` equals `squaredBuresHermitian B A` and is Fréchet
differentiable in `A` at every positive-definite pair. This uses the actual
CFC matrix square root, whose ordinary real derivative was proved in
`HermitianSquareSmooth.lean` by a local inverse of Hermitian squaring.

`BuresCoordinatesCriterion.lean` proves an abstract local regularity theorem.
If a continuous map `F` preserves a family of coordinates `Cdst ∘ F = Csrc`,
`Csrc` is differentiable, and `Cdst` has an invertible strict derivative at
`F(A)`, then `F` is differentiable at `A`. Its `contDiffAt_one_of_preserves_coordinates`
version gives C¹ regularity when the two coordinate maps are C¹. The finite
family `anchoredSquaredDistances` is differentiable at every positive-definite
base point if its anchors are positive definite.

To apply this to an arbitrary Bures distance-preserving self-map in matrix
size `n`, choose `n²` positive-definite anchors `B_i` near `A` and use the
coordinate maps

    Csrc(X)_i = distance(X, B_i)^2,
    Cdst(Y)_i = distance(Y, F(B_i))^2.

Distance preservation gives `Cdst(F(X)) = Csrc(X)` exactly. The missing
nondegeneracy statement is that, for some such anchors, the Jacobian
`D Cdst(F(A))` is a real-linear isomorphism. To call the compiled abstract C¹
criterion, one also needs C¹ (rather than merely pointwise differentiability)
of these literal coordinate maps near their base points and a real-linear
identification of Hermitian matrices with `ℝ^(n²)`.

The expected geometric mechanism is the first-variation identity for squared
distance: as an anchor moves from the base point in an independent tangent
direction, its coordinate differential approaches minus twice the Bures metric
dual of that direction. This first variation and the nondegenerate-anchor
choice have not yet been formalized. There is a further image issue: the
target anchors must be `F(B_i)`, so a proof that the isometric embedding has
locally open image (for example, an invariance-of-domain result) would let one
choose suitable target anchors and pull them back. Neither openness of the
image nor the anchor Jacobian is currently proved by the compiled files.

The present differentiation result does not yet prove smoothness of `F`, the
curvature-based radial identification, trace preservation, or surjectivity.
