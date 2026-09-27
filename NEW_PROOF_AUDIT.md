# Independent audit of the normal-coordinate proof

Audited on 2026-09-27. The target in `Bures.lean` is the literal complex-matrix Bures distance
`sqrt (Tr A + Tr B - 2 Tr sqrt (sqrt A * B * sqrt A))`, for every matrix size `n ≥ 2`.
`AutomaticSurjectivity` assumes only preservation of this distance; `LiteratureProblem`
uses the cited paper's equivalent normalization. Neither definition assumes continuity,
trace preservation, or surjectivity.

The mathematical argument in `NORMAL_COORDINATE_PROOF.md` matches the compiled
supporting theorem chain. Midpoint contraction and the differentiated optimal-lift
formula establish a local Hilbert-space isometry. `local_hilbert_isometry_linear`
extends it to a linear isometric embedding without assuming the original map is onto;
finite-dimensionality upgrades the embedding to a linear equivalence, and midpoint
iteration extends the formula globally. This is assembled without extra hypotheses by
`isometry_global_normal_representation` in `BuresNormalIsometry.lean`.

The affine normal form gives `F(T²)=P(T) C P(T)` for positive `T`, where
`P(T)=I+L(T-I)` and `C=F(I)`. The proposed homogeneous limit is
`Φ(X)=L(√X) C L(√X)`. The limit calculation on positive-definite inputs, continuity
of `Φ`, density, and the isometry estimate yield a PSD-cone isometry if the
isometric PSD extension of `F` is used. An isometry fixing the cone origin preserves
trace, and compact trace sublevels make `Φ` onto. Fidelity then identifies the
positive-definite stratum; together with positivity of affine factors this makes
`L` map the positive-definite cone onto itself. The Lean lemmas for each of these
*conditional* steps are in `BuresNormalBlowdown.lean`.

After that, `D=L⁻¹(I)-I` is positive semidefinite, and the affine form factors as
`F=Φ ∘ H_D` with `H_D(X)=(√X+D)²`. The compiled
`squareTranslation_displacement_zero` proves that an isometric `H_D` has `D=0`
for `n≥2`: first `D` commutes with every positive matrix and is scalar; a positive
scalar shift would force an optimal unitary to equal the identity and hence make
an explicitly chosen noncommuting pair commute. Zero displacement gives trace
preservation, then the established PSD-completion argument gives surjectivity.
`surjective_of_normal_representation_and_blowdown` assembles this implication.

**Final bridge completed:** `normalBlowdown_isometry_of_normal_form` in
`BuresNormalBlowdown.lean` takes the unconditional normal representation,
extends `F` isometrically to the PSD completion, proves the affine blowdown
limit on positive-definite inputs, extends convergence to the full cone by
density and continuity, and concludes that the specific quadratic model is
an isometry. `automaticSurjectivity` supplies this result to the assembly
theorem for every `n≥2`; `literatureProblem` transfers the theorem to the
paper's distance normalization through `exact_problem_equivalence`.

I independently compiled `BuresAutomaticSurjectivity.lean` with the repository's
pinned Lean environment after the final bridge was added (exit 0, about 20 s).
Lean reported exactly `[propext, Classical.choice, Quot.sound]` for each of
`surjective_of_normal_representation_and_blowdown`, `automaticSurjectivity`,
and `literatureProblem`. A scan of the project's top-level Lean files found no
declarations beginning with `axiom`, `opaque`, `sorry`, `admit`, or `unsafe`.
The scan excludes vendored Mathlib source.
