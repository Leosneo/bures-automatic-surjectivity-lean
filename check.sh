#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ ! -d "$project_dir/mathlib" ]; then
  cd "$project_dir"
  if [ ! -d .lake/packages/mathlib ]; then
    lake update
  fi
  lake exe cache get
  lake build BuresAutomaticSurjectivity
  exit 0
fi
cd "$project_dir/mathlib"
export LEAN_PATH="..${LEAN_PATH:+:$LEAN_PATH}"
for module in \
  Bures Sylvester BuresSquareDerivative BuresTopology \
  HermitianSquareSmooth BuresRadial BuresRadicand BuresSymmetry \
  BuresSquaredSmooth BuresCoordinatesCriterion HermitianFiniteDimension HermitianSylvesterSmooth \
  BuresVariational TraceCompactness BuresTriangle BuresFrobenius \
  BuresAnchorDerivative BuresInterior BuresPSD BuresFourPoint \
  BuresConeGeometry BuresApexFourPoint RadialAlgebra BuresCoordinateCurvature \
  BuresInfinitesimalMetric BuresOptimalLift BuresOptimalLiftSmooth BuresOptimalLiftJointSmooth \
  BuresNormComparison BuresInteriorTangent BuresSeparation BuresPSDMetric \
  BuresApexImageInterior BuresApexTangentTransfer BuresInteriorFourPoint BuresFourPointGeneral \
  BuresApexNotInteriorGeneral BuresQuotientGeodesic BuresGeodesicRigidity BuresUniqueGeodesic \
  BuresNormalChart BuresNormalTangent BuresMidpointIteration BuresImageSimplex \
  BuresMetricSimplexStability BuresIsometrySmoothPrelude BuresNormalLinearExtension BuresVerticalBracket \
  BuresIsometrySmoothTangent BuresNormalIsometry BuresCommutingProduct BuresSquareTranslation \
  BuresNormalForm BuresMetric BuresCompletion IsometryExtension \
  CompactSurjectivity BuresExtension BuresNormalBlowdown BuresNormalNormalization \
  BuresShiftTrace BuresShiftStrict BuresNoncommuting BuresTranslationRigidity \
  BuresConnectionAlgebra BuresCurvatureAtIdentityAlgebra BuresHorizontalLocal \
  BuresLocalRegularity BuresImageAnchorCoordinates BuresMetricAudit BuresMetricTangents \
  BuresMetricHomogeneity BuresQubitFidelity BuresQubitTangent BuresQubitUnitary \
  BuresQuotientPathLength BuresRankOneFourPoint RadialScaleRigidity \
  BuresAutomaticSurjectivity
do
  lake env lean --root=.. -o "../$module.olean" "../$module.lean"
done
