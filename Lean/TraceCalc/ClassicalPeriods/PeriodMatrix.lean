import TraceCalc.ClassicalPeriods.StructuredComparison

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Explicit Betti-side choice used to read coordinates from a structured comparison. -/
structure BettiBasisChoice
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    {betti : BettiRealization ctx generator}
    {deRham : DeRhamRealization ctx generator}
    (comparison : StructuredComparisonIso betti deRham) where
  basisIndex : Type y
  basisVector : basisIndex → comparison.BettiOverScalar
  coordinateReadout : basisIndex → comparison.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  basisLabel : basisIndex → String

/-- Explicit de Rham-side choice used to feed vectors into a structured comparison. -/
structure DeRhamBasisChoice
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    {betti : BettiRealization ctx generator}
    {deRham : DeRhamRealization ctx generator}
    (comparison : StructuredComparisonIso betti deRham) where
  basisIndex : Type z
  basisVector : basisIndex → comparison.DeRhamOverScalar
  basisLabel : basisIndex → String

/-- One scalar entry of a period matrix, obtained by applying a Betti readout to the comparison of a
chosen de Rham vector. -/
structure PeriodMatrixEntry
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    {betti : BettiRealization ctx generator}
    {deRham : DeRhamRealization ctx generator}
    {comparison : StructuredComparisonIso betti deRham}
    (bettiBasis : BettiBasisChoice comparison)
    (deRhamBasis : DeRhamBasisChoice comparison) where
  bettiSlot : bettiBasis.basisIndex
  deRhamSlot : deRhamBasis.basisIndex
  comparedVector : comparison.BettiOverScalar
  scalarValue : ctx.ScalarField
  scalar_eq_readout :
    scalarValue = bettiBasis.coordinateReadout bettiSlot
      (comparison.comparisonIso (deRhamBasis.basisVector deRhamSlot))

/-- Period matrix packet attached to one generator and one structured comparison datum. -/
structure PeriodMatrix
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx)
    (generator : FormalPeriodGenerator ctx) where
  comparison :
    StructuredComparisonIso
      (package.periodPackage.bettiOf generator)
      (package.periodPackage.deRhamOf generator) := package.comparisonOf generator
  bettiBasis : BettiBasisChoice comparison
  deRhamBasis : DeRhamBasisChoice comparison
  entry : bettiBasis.basisIndex → deRhamBasis.basisIndex →
    PeriodMatrixEntry bettiBasis deRhamBasis
  entry_agrees : ∀ (i : bettiBasis.basisIndex) (j : deRhamBasis.basisIndex),
    (entry i j).scalarValue =
      bettiBasis.coordinateReadout i (comparison.comparisonIso (deRhamBasis.basisVector j))

/-- A scalar period read from an explicit matrix entry. -/
structure ScalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    (matrix : PeriodMatrix package generator) where
  bettiSlot : matrix.bettiBasis.basisIndex
  deRhamSlot : matrix.deRhamBasis.basisIndex
  matrixEntry : PeriodMatrixEntry matrix.bettiBasis matrix.deRhamBasis
  scalarValue : ctx.ScalarField
  scalar_eq_matrix_entry : scalarValue = matrixEntry.scalarValue

/-- Coarse scalar period data remembers the formal expression whose scalar value is read through the
structured comparison package. -/
structure CoarseScalarPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    (package : StructuredComparisonPackage ctx) where
  expression : FormalPeriodExpression ctx
  scalarValue : ctx.ScalarField
  scalar_eq_expression_eval :
    scalarValue = package.periodPackage.scalarOfExpression expression

/-- A scalar shadow derived from a period matrix entry and the structured-comparison scalar
interface for the same generator. -/
structure StructuredToScalarShadow
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    (matrix : PeriodMatrix package generator) where
  scalarPeriod : ScalarPeriod matrix
  structuredShadow : StructuredComparisonScalarShadow package generator
  scalarValue : ctx.ScalarField
  scalar_eq_period_entry : scalarValue = scalarPeriod.scalarValue
  packageScalarValue : ctx.ScalarField
  packageScalar_eq_eval : packageScalarValue = package.periodPackage.scalarOfGenerator generator

/-- Explicit basis-change data between two choices for the same structured comparison. -/
structure BasisChangeData
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    {betti : BettiRealization ctx generator}
    {deRham : DeRhamRealization ctx generator}
    {comparison : StructuredComparisonIso betti deRham}
    (sourceBetti targetBetti : BettiBasisChoice comparison)
    (sourceDeRham targetDeRham : DeRhamBasisChoice comparison) where
  BettiChangeCertificate : Type w
  DeRhamChangeCertificate : Type x
  bettiCertificate : BettiChangeCertificate
  deRhamCertificate : DeRhamChangeCertificate
  bettiIndexMap : sourceBetti.basisIndex → targetBetti.basisIndex
  deRhamIndexMap : sourceDeRham.basisIndex → targetDeRham.basisIndex
  bettiVectorMap : sourceBetti.basisIndex → comparison.BettiOverScalar
  deRhamVectorMap : sourceDeRham.basisIndex → comparison.DeRhamOverScalar
  betti_vector_eq_target : ∀ i : sourceBetti.basisIndex,
    bettiVectorMap i = targetBetti.basisVector (bettiIndexMap i)
  deRham_vector_eq_target : ∀ j : sourceDeRham.basisIndex,
    deRhamVectorMap j = targetDeRham.basisVector (deRhamIndexMap j)

/-- Compatibility record comparing matrix entries before and after an explicit basis change. -/
structure BasisChangeCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    {generator : FormalPeriodGenerator ctx}
    {betti : BettiRealization ctx generator}
    {deRham : DeRhamRealization ctx generator}
    {comparison : StructuredComparisonIso betti deRham}
    (sourceBetti targetBetti : BettiBasisChoice comparison)
    (sourceDeRham targetDeRham : DeRhamBasisChoice comparison) where
  basisChange :
    BasisChangeData sourceBetti targetBetti sourceDeRham targetDeRham
  transformedEntry :
    sourceBetti.basisIndex → sourceDeRham.basisIndex → ctx.ScalarField
  targetEntry : targetBetti.basisIndex → targetDeRham.basisIndex → ctx.ScalarField
  transformedEntry_eq_target : ∀ (i : sourceBetti.basisIndex)
      (j : sourceDeRham.basisIndex),
    transformedEntry i j = targetEntry (basisChange.bettiIndexMap i) (basisChange.deRhamIndexMap j)

namespace PeriodMatrix

/-- Matrix entry as a scalar. -/
def scalarEntry
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    (matrix : PeriodMatrix package generator)
    (i : matrix.bettiBasis.basisIndex)
    (j : matrix.deRhamBasis.basisIndex) : ctx.ScalarField :=
  (matrix.entry i j).scalarValue

@[simp] theorem scalarEntry_eq_readout
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    (matrix : PeriodMatrix package generator)
    (i : matrix.bettiBasis.basisIndex)
    (j : matrix.deRhamBasis.basisIndex) :
    matrix.scalarEntry i j =
      matrix.bettiBasis.coordinateReadout i
        (matrix.comparison.comparisonIso (matrix.deRhamBasis.basisVector j)) :=
  matrix.entry_agrees i j

/-- Scalar period associated to a matrix slot. -/
def scalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    (matrix : PeriodMatrix package generator)
    (i : matrix.bettiBasis.basisIndex)
    (j : matrix.deRhamBasis.basisIndex) : ScalarPeriod matrix where
  bettiSlot := i
  deRhamSlot := j
  matrixEntry := matrix.entry i j
  scalarValue := matrix.scalarEntry i j
  scalar_eq_matrix_entry := rfl

end PeriodMatrix

namespace StructuredToScalarShadow

/-- Scalar value exposed by the matrix-entry shadow. -/
def scalar
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    {matrix : PeriodMatrix package generator}
    (shadow : StructuredToScalarShadow matrix) : ctx.ScalarField :=
  shadow.scalarValue

@[simp] theorem scalar_eq_entry
    {ctx : ClassicalComparisonContext.{u, v}}
    {package : StructuredComparisonPackage ctx}
    {generator : FormalPeriodGenerator ctx}
    {matrix : PeriodMatrix package generator}
    (shadow : StructuredToScalarShadow matrix) :
    shadow.scalar = shadow.scalarPeriod.scalarValue :=
  shadow.scalar_eq_period_entry

end StructuredToScalarShadow

end ClassicalPeriods
end TraceCalc
