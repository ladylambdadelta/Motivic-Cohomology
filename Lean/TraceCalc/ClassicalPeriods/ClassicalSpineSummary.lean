import TraceCalc.ClassicalPeriods.GeneratorRealizationExamples

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- Readable dependency spine for the completed ClassicalPeriods generator layer.

This packages the assignment-table side together with the geometric tomography package and the
single realization-compatibility witness needed to recover the generator-family package, the
localization package, and the readiness target by forgetful projection. -/
structure ClassicalPeriodsSpine
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  assignmentTable : GeneratorRealizationAssignmentTable ctx
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  sharedRealizationTarget :
    assignmentTable.realization = tomographySoundness.geometricRealizationFunctor

namespace ClassicalPeriodsSpine

/-- Realization functor shared across the assignment/localization/tomography spine. -/
abbrev realization
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : ClassicalPeriodsSpine ctx structuredEq) :
    GeometricRealizationFunctorData ctx :=
  spine.assignmentTable.realization

/-- Named generator-family package obtained from the assignment table. -/
abbrev generatorFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : ClassicalPeriodsSpine ctx structuredEq) : GeometricGeneratorFamilyPackage ctx :=
  spine.assignmentTable.toGeometricGeneratorFamilyPackage

/-- Localization/descent package obtained from the assignment table. -/
abbrev localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : ClassicalPeriodsSpine ctx structuredEq) : GeometricLocalizationPackage ctx :=
  spine.assignmentTable.toGeometricLocalizationPackage

/-- Motivic-readiness package obtained from the assignment table and tomography soundness. -/
abbrev readiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : ClassicalPeriodsSpine ctx structuredEq) :
    ClassicalMotivicRealizationReadiness ctx structuredEq :=
  spine.assignmentTable.toClassicalMotivicRealizationReadiness
    spine.tomographySoundness
    spine.sharedRealizationTarget

end ClassicalPeriodsSpine

namespace GeneratorRealizationAssignmentTable

/-- Build the readable ClassicalPeriods spine from an assignment table and tomography soundness. -/
def toClassicalPeriodsSpine
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    ClassicalPeriodsSpine ctx structuredEq where
  assignmentTable := table
  tomographySoundness := tomography
  sharedRealizationTarget := hrealization

@[simp] theorem toClassicalPeriodsSpine_assignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).assignmentTable = table := rfl

@[simp] theorem toClassicalPeriodsSpine_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).tomographySoundness = tomography := rfl

@[simp] theorem toClassicalPeriodsSpine_sharedRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).sharedRealizationTarget = hrealization :=
  rfl

@[simp] theorem toClassicalPeriodsSpine_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).realization = table.realization := rfl

@[simp] theorem toClassicalPeriodsSpine_generatorFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).generatorFamilyPackage =
      table.toGeometricGeneratorFamilyPackage := rfl

@[simp] theorem toClassicalPeriodsSpine_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).localizationPackage =
      table.toGeometricLocalizationPackage := rfl

@[simp] theorem toClassicalPeriodsSpine_readiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toClassicalPeriodsSpine tomography hrealization).readiness =
      table.toClassicalMotivicRealizationReadiness tomography hrealization := rfl

end GeneratorRealizationAssignmentTable

/-- Generic row-wise symbolic spine piece for the `Corr` row. -/
structure CorrGeneratorRowSpinePiece
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  family : CorrGeneratorFamilyData ctx realization
  assignment : CorrGeneratorRealizationAssignment ctx realization

/-- Generic row-wise symbolic spine piece for the `Loc` row. -/
structure LocGeneratorRowSpinePiece
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  family : LocGeneratorFamilyData ctx realization
  assignment : LocGeneratorRealizationAssignment ctx realization

/-- Generic row-wise symbolic spine piece for the `Nis` row. -/
structure NisGeneratorRowSpinePiece
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  family : NisGeneratorFamilyData ctx realization
  assignment : NisGeneratorRealizationAssignment ctx realization

/-- Generic row-wise symbolic spine piece for the `A1` row. -/
structure A1GeneratorRowSpinePiece
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  family : A1GeneratorFamilyData ctx realization
  assignment : A1GeneratorRealizationAssignment ctx realization

/-- Generic row-wise symbolic spine piece for the `Env` row. -/
structure EnvGeneratorRowSpinePiece
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  family : EnvGeneratorFamilyData ctx realization
  assignment : EnvGeneratorRealizationAssignment ctx realization

/-- The unit sanity model inhabits the full ClassicalPeriods dependency spine. -/
def unitClassicalPeriodsSpine
    (ctx : ClassicalComparisonContext.{u, v}) :
    ClassicalPeriodsSpine ctx (unitStructuredComparisonEquality ctx) :=
  (unitGeneratorRealizationAssignmentTable ctx).toClassicalPeriodsSpine
    (unitGeometricRealizationTomographySoundness ctx)
    rfl

end ClassicalPeriods
end TraceCalc