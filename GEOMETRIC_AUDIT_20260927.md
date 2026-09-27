# Geometric audit and exact outstanding obligation

This audit concerns the literal Bures formula in `Bures.lean`, not the ambient
matrix norm. The supporting algebra below compiles, but automatic surjectivity
has not been proved by those files.

## Newly verified algebra

`RadialAlgebra.lean` proves that a Hermitian complex matrix commutes with every
Hermitian matrix exactly when it is a real scalar multiple of the identity.
It also proves that the Sylvester image of this common commutant is exactly
the radial line `{c A : c in R}`. The proof uses the real/imaginary self-adjoint
decomposition of arbitrary complex matrices and mathlib's matrix-center lemma.

`Sylvester.lean` proves that, for positive-definite A and arbitrary complex X,
there is a unique K with `K A + A K = X`. If X is Hermitian, K is Hermitian.
The proof conjugates by A's unitary eigenvector matrix and divides the (i,j)
entry by the strictly positive sum of eigenvalues. These are unconditional
matrix theorems; no curvature, isometry regularity, or trace-preservation
hypothesis is added.

The principal new declarations report only `propext`, `Classical.choice`,
and `Quot.sound` as axioms.

## Exact central missing theorem

In existing notation, the required rigidity claim is

```lean
∀ n : ℕ, 2 ≤ n → ∀ F : PositiveDefinite n → PositiveDefinite n,
  PreservesDistance F → ∀ A, tr (F A).val = tr A.val
```

Neither the common-commutant result nor the Sylvester inverse establishes this
claim. To apply them, one must connect the literal distance to differentiable
quotient geometry and prove that a distance-preserving map transports the
curvature data. Assuming that bridge would assume the central missing work.

The following geometric obligations remain separate:

1. The displayed square-root formula agrees with the quotient **Riemannian
   path distance**. The attained unitary metric-quotient formula and ordinary
   topology are now proved in `BuresTriangle.lean` and the metric modules, but
   those do not establish the differential-geometric identification.
2. Distance-preserving selfmaps of the open cone have the smooth local-isometry
   structure required to transport tangent vectors, connection and curvature.
3. The quotient metric has the stated O'Neill curvature formula and its Euler
   field has covariant derivative equal to the identity.

The previous fourth obligation is now completed: `BuresCompletion.lean` and
`BuresExtension.lean` link the actual PSD completion, compact trace sublevels
and positive-definite interior to the literal formula. The resulting
`surjective_of_preserves_trace` still has an explicit trace-preservation
hypothesis and is not the unconditional target.

A source search of the pinned mathlib geometry files found Riemannian path
lengths and distance topology, but no ready-to-use Myers–Steenrod theorem,
O'Neill formula, or the needed quotient-connection development. This is a
statement about this inspected checkout, not all public Lean projects.

## Informal argument audit

The proposed geometric argument is internally consistent under its classical
geometric inputs. At an invertible lift S, horizontal vectors are K S with K
Hermitian. The fixed-generator horizontal fields have bracket [L,K] S. If its
vertical component is zero, invertibility of S makes [L,K] Hermitian; since
it is also skew-Hermitian it vanishes. O'Neill's formula would consequently
identify the common zero-sectional-curvature locus with the real radial line.

The Euler field Z(A)=2A has horizontal lift S. Its covariant derivative is the
identity and its squared norm is Tr(A). If a local isometry pushes it to f Z,
connection preservation gives `(1-f)Y = Y(f)Z`. A tangent direction independent
of Z forces f=1. This uses dimension greater than one and correctly excludes
the scalar square-root translation counterexamples.

There is no identified contradiction in this informal chain, but this audit
does not replace proofs of its classical differential-geometric inputs in Lean.

## Assessment of a curvature-free route

Explicit Bures geodesics are potential replacements for the quotient curvature
machinery: one would first characterize metric-preserving maps on local
geodesics and derive an intrinsic radial direction from that characterization.
This is not presently a complete alternative proof. In particular, observing
that rays map to geodesics does not prove that their common limiting image is
the zero matrix. A nonzero positive-semidefinite limiting image is exactly the
possibility that must be ruled out; ruling it out by assumption would be
circular. The scalar example shows that cone geometry and geodesic preservation
alone cannot establish the desired conclusion.
