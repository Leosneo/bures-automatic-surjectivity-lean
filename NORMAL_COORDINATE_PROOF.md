# Automatic surjectivity through normal coordinates

This proof concerns the literal Bures–Wasserstein distance on positive
definite complex Hermitian matrices of size `n ≥ 2`. It replaces the
earlier draft's Riemannian curvature argument with midpoint rigidity and
the unitary variational formula. The Lean status is recorded in README.md;
the mathematical argument below does not itself certify compilation.

Write

\[
d(A,B)^2=\operatorname{Tr}A+\operatorname{Tr}B
 -2\operatorname{Tr}\sqrt{\sqrt A B\sqrt A}.
\]

For a fixed positive definite matrix `A`, put `S=√A` and define positive
transport and centered normal coordinates by

\[
T_A(B)=S^{-1}\sqrt{SBS}\,S^{-1},\qquad K_A(B)=T_A(B)-I.
\]

Then `T_A(B)>0` and `B=T_A(B) A T_A(B)`. Thus the normal-coordinate domain
is exactly the open set of Hermitian `K` with `I+K>0`. Its tangent norm is
`‖K S‖_F`.

## 1. Isometries are globally linear in normal coordinates

The optimal factor of `B` relative to `S` is
`O_A(B)=S⁻¹√(SBS)=T_A(B)S`, and
`d(A,B)=‖S−O_A(B)‖_F`. Optimal alignment is unique for positive definite
endpoints. The metric midpoint `M` of `A,B` therefore satisfies

\[
O_A(M)=\frac{S+O_A(B)}2,\qquad K_A(M)=\frac{K_A(B)}2.
\]

Let `B_k` be obtained by taking this midpoint `k` times. Every
distance-preserving map `F` preserves these midpoints. In particular,
`K_A(B_k)=2^{-k}K_A(B)`, and the same identity holds after applying `F`.

The differentiated literal square-root formula supplies the two-point
tangent-distance limit

\[
\lim_{k\to\infty}2^k d(B_k,C_k)
 =\|(K_A(B)-K_A(C))\sqrt A\|_F.
\]

Applying the same limit at `F(A)` and using distance preservation shows
that the map between the two normal-coordinate domains preserves their
Hilbert norms of differences exactly. It fixes the origin. On a small
ball it consequently agrees with a real linear isometry: one extends
the ball map by repeated halving, then applies the affine-isometry
theorem for strictly convex real normed spaces. The source and target
have the same finite dimension, so this linear map is a linear
equivalence. Repeated halving extends its formula to every point of the
normal-coordinate domain.

At the base point `I`, write `C=F(I)`. There is a real linear equivalence
`L` on Hermitian matrices such that, for every positive definite `T`,

\[
P(T)=I+L(T-I)>0,\qquad F(T^2)=P(T)C P(T).
\]

This conclusion assumes only preservation of the displayed Bures distance.

## 2. The homogeneous limit is onto

Define on the positive semidefinite cone

\[
\Phi(X)=L(\sqrt X)\,C\,L(\sqrt X).
\]

For positive definite `X=T²`, the affine formula gives

\[
r^{-2}F(r^2X)
 =\bigl(L(T)+r^{-1}(I-L(I))\bigr)
 C\bigl(L(T)+r^{-1}(I-L(I))\bigr)
 \longrightarrow\Phi(X).
\]

The Bures distance scales as `d(sX,sY)=√s d(X,Y)`. Every rescaled map is
therefore an isometry. Extend `F` to the complete positive semidefinite
cone. Continuity of `Φ`, density of the positive definite cone, and the
isometry estimates extend the above convergence to every semidefinite
input. It follows that `Φ` is a Bures isometry and `Φ(0)=0`.

Since `d(X,0)²=Tr X`, `Φ` preserves trace. Each semidefinite trace sublevel
is compact. An isometric self-map of a compact metric space is onto, so
`Φ` is onto the entire semidefinite cone. Fidelity preservation then
shows that it preserves the positive definite stratum in both
directions: positive definiteness is characterized by having nonzero
fidelity with every nonzero positive semidefinite matrix.

The affine factors `P(rT)>0`, divided by `r` and sent to infinity, imply
`L(T)≥0` for every `T>0`. Since `Φ(T²)>0`, its factor `L(T)` is invertible,
and hence `L(T)>0`. Conversely, given `Y>0`, surjectivity of `Φ` gives
`Φ(X)=YCY`. The input `X` is positive definite. Uniqueness of positive
transport yields `L(√X)=Y`. Thus `L` maps the positive definite cone onto
itself.

## 3. Normalize to a square-root translation

Set `D=L⁻¹(I)−I`. For every `T>0`, positivity of `P(T)` and positivity of
the inverse linear map give `T+D>0`. Taking `T=εI` and `ε↓0` proves
`D≥0`. Linearity gives

\[
P(T)=L(T+D),\qquad
F(X)=\Phi\bigl((\sqrt X+D)^2\bigr).
\]

Because both `F` and `Φ` preserve Bures distance, the map
`H_D(X)=(√X+D)²` preserves Bures distance.

## 4. A square-root translation must vanish

For positive definite roots `T,S`, equality

\[
d(T^2,S^2)=\|T-S\|_F
\]

holds exactly when `T,S` commute. The forward implication follows from
uniqueness of the optimal alignment: the identity alignment is optimal,
so `TS` is positive Hermitian. The reverse implication follows from
positivity of a product of commuting positive matrices.

Apply this criterion to `T` and `I`, and to their translated roots
`T+D` and `I+D`. If `H_D` is an isometry, the translated roots commute,
which implies `[T,D]=0`. Every Hermitian direction is a scalar multiple
of a small positive perturbation of `I`, so `D` commutes with every
Hermitian matrix. Consequently `D=cI`, with `c≥0`.

Suppose `c>0`. Choose positive definite `T,S` that do not commute; such
matrices exist for every `n≥2`. Let `U` be an optimal unitary for the
shifted roots. The variational formula and the inequalities
`ReTr(TU)≤Tr T`, `ReTr(SU)≤Tr S`, and `ReTr U≤Tr I` give

\[
\begin{aligned}
\operatorname{ReTr}((T+cI)(S+cI)U)
&\leq \operatorname{fid}(T^2,S^2)
   +c\operatorname{Tr}T+c\operatorname{Tr}S+c^2\operatorname{Tr}I.
\end{aligned}
\]

Preservation of distance forces equality in this bound. All its losses
are nonnegative, so `c²(Tr I−ReTr U)=0`. Hence `U=I`. The unshifted
identity alignment must then also be optimal, forcing `T,S` to commute,
a contradiction. Thus `c=0` and `D=0`.

We have `F=Φ` on the positive definite cone. In particular `F` preserves
trace, and the checked completion-and-compactness argument proves that
`F` is surjective. The one-dimensional counterexample
`a↦(√a+c)²` explains why `n≥2` is necessary.

## Relation to the original draft

Both arguments use the Gram factorization, positive transport, and
noncommutativity. The present proof detects noncommutativity through
strictness in optimal unitary alignment. It does not invoke a quotient
Riemannian construction, Myers–Steenrod, O'Neill curvature, or a
Levi-Civita connection. Those earlier geometric proof obligations are
therefore unnecessary for this formalization of the same theorem.

## Lean theorem map

| Mathematical step | Lean declaration | File |
| --- | --- | --- |
| Midpoint contraction | `normalCoordinate_midpointIteration` | `BuresMidpointIteration.lean` |
| Exact tangent norm preservation | `isometry_preserves_normal_coordinate_distance` | `BuresIsometrySmoothTangent.lean` |
| Global linear normal form | `isometry_global_normal_representation` | `BuresNormalIsometry.lean` |
| Homogeneous limit preserves Bures distance | `normalBlowdown_isometry_of_normal_form` | `BuresNormalBlowdown.lean` |
| The linear factor maps the positive cone onto itself | `normalBlowdown_linear_surjective_on_posDef` | `BuresNormalBlowdown.lean` |
| Remaining translation preserves distance | `squareTranslation_preserves_of_normal_form` | `BuresNormalNormalization.lean` |
| Translation vanishes for every n ≥ 2 | `squareTranslation_displacement_zero` | `BuresTranslationRigidity.lean` |
| Trace preservation implies surjectivity | `surjective_of_preserves_trace` | `BuresExtension.lean` |
| Unconditional conclusion and literature normalization | `automaticSurjectivity`, `literatureProblem` | `BuresAutomaticSurjectivity.lean` |
