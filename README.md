# Automatic surjectivity of Bures–Wasserstein isometries

This repository formalizes the **p = 2, matrix size n ≥ 2** case of the automatic-surjectivity problem posed by Komálovics and Molnár after Proposition 10 of [*On a parametric family of distance measures that includes the Hellinger and the Bures distances*](https://publicatio.bibl.u-szeged.hu/37355/1/OnaparametricfamilyofdistancemeasuresthatincludestheHellingerandtheBuresdistances_ML.pdf). It does not address other values of p. The restriction n ≥ 2 is necessary: in dimension one, a ↦ (√a + c)² with c > 0 preserves Bures distance but is not surjective.

The main theorems are `Bures.automaticSurjectivity : AutomaticSurjectivity` and `Bures.literatureProblem : LiteratureProblem` in [`BuresAutomaticSurjectivity.lean`](BuresAutomaticSurjectivity.lean). They are unconditional: every self-map of positive definite complex Hermitian n × n matrices preserving the **literal** Bures distance is surjective. The definition in [`Bures.lean`](Bures.lean) uses mathlib's `Matrix.PosDef`, canonical positive square root, and matrix trace:

```text
d(A,B) = √(Tr A + Tr B − 2 Tr √(√A B √A)).
```

The paper's `d₂` differs by the constant factor 1/√2. `preserves_iff_literature` and `exact_problem_equivalence` prove that distance preservation and the theorem statement are unchanged by this normalization. The theorem assumes no continuity, differentiability, trace preservation, or prior surjectivity.

The proof uses unique Bures metric midpoints to obtain exact dyadic contractions in positive-transport normal coordinates. Differentiating the literal distance along those contractions shows that an isometry preserves the Hilbert tangent norm. Its normal-coordinate action is therefore locally linear and, by repeated halving, globally linear. A rescaling limit on the positive semidefinite completion produces a surjective homogeneous isometry. Factoring the original map through that limit leaves a square-root translation; strict optimal-unitary alignment rules out every nonzero translation when n ≥ 2. Trace preservation and surjectivity then follow. The full mathematical argument and its correspondence with the Lean modules are in [`NORMAL_COORDINATE_PROOF.md`](NORMAL_COORDINATE_PROOF.md).

The earlier curvature-based draft is not needed for this proof. [`GEOMETRIC_AUDIT_20260927.md`](GEOMETRIC_AUDIT_20260927.md), [`FORMALIZATION_GAPS.md`](FORMALIZATION_GAPS.md), and [`LOCAL_SMOOTHNESS_AUDIT.md`](LOCAL_SMOOTHNESS_AUDIT.md) record historical gaps in that superseded route; their old “unproved” status statements do not describe the normal-coordinate proof. [`NEW_PROOF_AUDIT.md`](NEW_PROOF_AUDIT.md) audits the completed route.

## Reproduce

The project pins Lean `v4.29.1` in [`lean-toolchain`](lean-toolchain) and mathlib4 commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` in [`lakefile.lean`](lakefile.lean). From this directory run:

```sh
sh check.sh
```

With the existing `mathlib/` checkout, the script compiles every local source in dependency order and prints axiom audits for the key results. On a fresh checkout without that directory, it fetches the pinned Lake dependencies and mathlib cache, then builds the library containing all local Lean modules. The main theorem's direct compilation and `#print axioms` report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The full 79-module source rebuild completed successfully on 27 September 2026 (exit 0) in 527.138 seconds. Both final theorems report exactly these standard axioms. See the [complete build log](verification_normal_full_20260927.log) and [verification record with source hashes](verification_normal_full_20260927.json). Earlier verification files are retained as historical intermediate states; their incomplete-status statements are superseded by this full run.
