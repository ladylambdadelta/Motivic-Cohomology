import TraceCalc.ClassicalPeriods.GeometricPeriodSpine
import TraceCalc.ClassicalPeriods.GeneratorRealizationExamples
import TraceCalc.ClassicalPeriods.SymbolicGeneratorExamples

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- The unit sanity model inhabits the readable dependency spine. -/
def unitClassicalPeriodsSpine
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricPeriodSpine ctx (unitStructuredComparisonEquality ctx) :=
  (unitGeneratorRealizationAssignmentTable ctx).toGeometricPeriodSpine
    (unitGeometricRealizationTomographySoundness ctx)
    rfl

/-- Row-wise spine packaging for the symbolic `Corr` generator example. -/
def symbolicCorrRowSpinePiece
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    CorrGeneratorRowSpinePiece ctx where
  realization := symbolicCorrRealizationFunctorData datum
  family := symbolicCorrGeneratorFamilyData datum
  assignment := symbolicCorrGeneratorRealizationAssignment datum

/-- Row-wise spine packaging for the symbolic `Loc` generator example. -/
def symbolicLocRowSpinePiece
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    LocGeneratorRowSpinePiece ctx :=
  LocGeneratorRowSpinePiece.ofFamilyAndAssignment
    (symbolicLocRealizationFunctorData datum)
    (symbolicLocGeneratorFamilyData datum)
    (symbolicLocGeneratorRealizationAssignment datum)

/-- Row-wise spine packaging for the symbolic `Nis` generator example. -/
def symbolicNisRowSpinePiece
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    NisGeneratorRowSpinePiece ctx :=
  NisGeneratorRowSpinePiece.ofFamilyAndAssignment
    (symbolicNisRealizationFunctorData datum)
    (symbolicNisGeneratorFamilyData datum)
    (symbolicNisGeneratorRealizationAssignment datum)

/-- Row-wise spine packaging for the symbolic `A1` generator example. -/
def symbolicA1RowSpinePiece
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    A1GeneratorRowSpinePiece ctx :=
  A1GeneratorRowSpinePiece.ofFamilyAndAssignment
    (symbolicA1RealizationFunctorData datum)
    (symbolicA1GeneratorFamilyData datum)
    (symbolicA1GeneratorRealizationAssignment datum)

/-- Row-wise spine packaging for the symbolic `Env` generator example. -/
def symbolicEnvRowSpinePiece
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    EnvGeneratorRowSpinePiece ctx :=
  EnvGeneratorRowSpinePiece.ofFamilyAndAssignment
    (symbolicEnvRealizationFunctorData datum)
    (symbolicEnvGeneratorFamilyData datum)
    (symbolicEnvGeneratorRealizationAssignment datum)

@[simp] theorem unitClassicalPeriodsSpine_assignmentTable
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitClassicalPeriodsSpine ctx).assignmentTable = unitGeneratorRealizationAssignmentTable ctx := rfl

@[simp] theorem unitClassicalPeriodsSpine_localizationPackage
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitClassicalPeriodsSpine ctx).localizationPackage =
      unitGeometricLocalizationPackageFromAssignmentTable ctx := rfl

@[simp] theorem symbolicCorrRowSpinePiece_family
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrRowSpinePiece datum).family = symbolicCorrGeneratorFamilyData datum := rfl

@[simp] theorem symbolicLocRowSpinePiece_family
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocRowSpinePiece datum).family = symbolicLocGeneratorFamilyData datum := rfl

@[simp] theorem symbolicNisRowSpinePiece_family
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisRowSpinePiece datum).family = symbolicNisGeneratorFamilyData datum := rfl

@[simp] theorem symbolicA1RowSpinePiece_family
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1RowSpinePiece datum).family = symbolicA1GeneratorFamilyData datum := rfl

@[simp] theorem symbolicEnvRowSpinePiece_family
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvRowSpinePiece datum).family = symbolicEnvGeneratorFamilyData datum := rfl

end ClassicalPeriods
end TraceCalc
