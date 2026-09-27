# Audit of the remaining automatic-surjectivity argument

This audit concerns the actual `Bures.AutomaticSurjectivity` proposition, not a
conditional substitute. The original project defines this proposition but does
not prove it. New supporting lemmas do not by themselves change that status.

## A completed simplification: return from PSD to PD

`BuresInterior.lean` replaces the second use of invariance of domain in the
informal draft by a matrix argument. It proves, for any positive semidefinite A,

    A.PosDef ↔ ∀ B ≥ 0, fidelityRoot A B = 0 → B = 0.

For positive definite A its positive square root is invertible. Zero fidelity
means its positive sandwich has zero square root trace; faithfulness of the
trace makes that sandwich zero, and invertibility implies B = 0. Conversely,
if the square root is singular, take a nonzero vector v in its kernel. The
nonzero positive semidefinite matrix vv* has zero fidelity with A.

Thus a bijection of the PSD cone which preserves zero and fidelity preserves
its PD stratum. The theorem `surjective_of_semidefinite_extension` then proves
surjectivity of an actual PD map given such an extension which agrees with it.
All these theorems use the literal CFC square root and matrix trace. They
compile with only `propext`, `Classical.choice`, and `Quot.sound`.

These are conditional extension/assembly results. `BuresCompletion.lean` and
`BuresExtension.lean` now prove that every distance-preserving PD map has an
isometric extension to the actual complete PSD cone. Compact trace sublevels
and the interior characterization prove `surjective_of_preserves_trace`, with
trace preservation still an explicit hypothesis. The definition of
`AutomaticSurjectivity` has not been changed to include that hypothesis.

## Positive semidefinite metric identities now checked

`BuresPSD.lean` extends positive-definite radicand nonnegativity to PSD
matrices using the explicit approximation A + I/(m+1), the proved continuity
of CFC square root, and the actual fidelity formula. It defines `psdDistance`
by this formula and proves its nonnegativity, self-distance, symmetry,
triangle inequality, squared-distance identity, and ordinary-topology
continuity. Separation, compatibility with the ordinary matrix topology,
properness and completeness are now proved in the other metric modules.

The same file proves that a distance-preserving PSD map **which fixes zero**
preserves trace and fidelity. The zero-fixing hypothesis is explicit. This
cannot be applied to an arbitrary extension until zero fixing has actually
been established; obtaining it is equivalent here to the missing trace
rigidity, not a way around it.

## Central dependency still requiring proof

The key unresolved assertion is trace preservation for an arbitrary map
preserving the explicit Bures formula. The existing informal argument has the
following dependencies:

1. The explicit formula defines the quotient Riemannian distance.
2. A distance-preserving map is a smooth local Riemannian isometry.
3. The quotient curvature has nullity exactly the radial line.
4. The Euler vector field satisfies ∇_X Z = X, with squared norm Tr A.
5. Naturality of the connection forces preservation of Z and hence trace.

Hermitian commutator algebra supplies part of step 3. It does not assert that
its algebraic expression is the curvature of this metric. Proving a theorem
assuming steps 1–4 does not discharge these dependencies.

## Pinned mathlib evidence

The pinned mathlib is commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
Its files `Geometry/Manifold/Riemannian/Basic.lean`,
`Geometry/Manifold/Riemannian/PathELength.lean`, and
`Geometry/Manifold/VectorBundle/Riemannian.lean` provide smooth Riemannian
bundles, path length, and the induced metric/topology framework.

A source search for Myers–Steenrod, O'Neill, Riemannian submersion,
Levi–Civita, sectional/Riemann curvature, invariance of domain, Bures, and
Wasserstein found no theorem implementing the needed results. This is a
bounded code search, not a proof that no alternative formal development exists
anywhere. It does establish that these steps cannot presently be discharged
by citing a theorem found in this project or pinned library.

## Alternate routes examined

The explicit geodesic formula suggests analyzing images of radial rays and
the image of zero in the completion. If that image were nonzero, one would
need to rule out an isometric copy of the whole cone based there. Merely
knowing the space is a cone, complete, or has compact trace sublevels does not
rule this out: translations of the scalar half-line are counterexamples.
A tangent-cone argument would itself need a rigidity invariant separating the
vertex from higher-rank points, plus proof that this invariant is preserved
by a full-dimensional embedding. This is not currently an elementary
replacement for the curvature argument.

The completed fidelity characterization above does remove the *final*
invariance-of-domain step. It does not remove the local smoothness step at the
beginning.

## Primary literature checked

- Bhatia, Jain, Lim, *On the Bures–Wasserstein distance between positive
  definite matrices*, Expositiones Mathematicae 37 (2019), 165–191:
  <https://doi.org/10.1016/j.exmath.2018.01.002>.
  This provides the matrix distance/geodesic and quotient framework.
- van Oostrum, *Bures–Wasserstein geometry for positive-definite Hermitian
  matrices and their trace-one subset*, Information Geometry (2022):
  <https://doi.org/10.1007/s41884-022-00069-7>.
  This develops the complex Hermitian quotient geometry.

A bounded web search on 2026-09-27 did not find a complete existing Lean
formalization of the missing rigidity argument or a source resolving it by a
ready-to-import elementary theorem. No claim of exhaustive priority search is
made.
