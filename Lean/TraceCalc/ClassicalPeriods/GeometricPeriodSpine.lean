import TraceCalc.ClassicalPeriods.GeneratorRealizationTable

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- Readable dependency spine for the completed ClassicalPeriods generator layer.

This packages the assignment-table side together with the geometric tomography package and the
single realization-compatibility witness needed to recover the generator-family package, the
localization package, and the readiness target by forgetful projection. -/
structure GeometricPeriodSpine
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  assignmentTable : GeneratorRealizationAssignmentTable ctx
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  sharedRealizationTarget :
    assignmentTable.realization = tomographySoundness.geometricRealizationFunctor

namespace GeometricPeriodSpine

/-- Realization functor shared across the assignment/localization/tomography spine. -/
abbrev realization
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : GeometricPeriodSpine ctx structuredEq) :
    GeometricRealizationFunctorData ctx :=
  spine.assignmentTable.realization

/-- Named generator-family package obtained from the assignment table. -/
abbrev generatorFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : GeometricPeriodSpine ctx structuredEq) : GeometricGeneratorFamilyPackage ctx :=
  spine.assignmentTable.toGeometricGeneratorFamilyPackage

/-- Localization/descent package obtained from the assignment table. -/
abbrev localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : GeometricPeriodSpine ctx structuredEq) : GeometricLocalizationPackage ctx :=
  spine.assignmentTable.toGeometricLocalizationPackage

/-- Motivic-readiness package obtained from the assignment table and tomography soundness. -/
abbrev readiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : GeometricPeriodSpine ctx structuredEq) :
    ClassicalMotivicRealizationReadiness ctx structuredEq :=
  spine.assignmentTable.toClassicalMotivicRealizationReadiness
    spine.tomographySoundness
    spine.sharedRealizationTarget

end GeometricPeriodSpine

namespace GeneratorRealizationAssignmentTable

/-- Build the readable ClassicalPeriods spine from an assignment table and tomography soundness. -/
def toGeometricPeriodSpine
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    GeometricPeriodSpine ctx structuredEq where
  assignmentTable := table
  tomographySoundness := tomography
  sharedRealizationTarget := hrealization

@[simp] theorem toGeometricPeriodSpine_assignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).assignmentTable = table := rfl

@[simp] theorem toGeometricPeriodSpine_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).tomographySoundness = tomography := rfl

@[simp] theorem toGeometricPeriodSpine_sharedRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).sharedRealizationTarget = hrealization :=
  rfl

@[simp] theorem toGeometricPeriodSpine_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).realization = table.realization := rfl

@[simp] theorem toGeometricPeriodSpine_generatorFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).generatorFamilyPackage =
      table.toGeometricGeneratorFamilyPackage := rfl

@[simp] theorem toGeometricPeriodSpine_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).localizationPackage =
      table.toGeometricLocalizationPackage := rfl

@[simp] theorem toGeometricPeriodSpine_readiness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (table : GeneratorRealizationAssignmentTable ctx)
    (tomography : GeometricRealizationTomographySoundness ctx structuredEq)
    (hrealization : table.realization = tomography.geometricRealizationFunctor) :
    (table.toGeometricPeriodSpine tomography hrealization).readiness =
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

namespace CorrGeneratorRowSpinePiece

def ofFamilyAndAssignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : CorrGeneratorFamilyData ctx realization)
  (assignment : CorrGeneratorRealizationAssignment ctx realization) :
  CorrGeneratorRowSpinePiece ctx where
  realization := realization
  family := family
  assignment := assignment

@[simp] theorem ofFamilyAndAssignment_realization
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : CorrGeneratorFamilyData ctx realization)
  (assignment : CorrGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).realization = realization := rfl

@[simp] theorem ofFamilyAndAssignment_family
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : CorrGeneratorFamilyData ctx realization)
  (assignment : CorrGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).family = family := rfl

@[simp] theorem ofFamilyAndAssignment_assignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : CorrGeneratorFamilyData ctx realization)
  (assignment : CorrGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).assignment = assignment := rfl

end CorrGeneratorRowSpinePiece

namespace LocGeneratorRowSpinePiece

def ofFamilyAndAssignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : LocGeneratorFamilyData ctx realization)
  (assignment : LocGeneratorRealizationAssignment ctx realization) :
  LocGeneratorRowSpinePiece ctx where
  realization := realization
  family := family
  assignment := assignment

@[simp] theorem ofFamilyAndAssignment_realization
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : LocGeneratorFamilyData ctx realization)
  (assignment : LocGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).realization = realization := rfl

@[simp] theorem ofFamilyAndAssignment_family
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : LocGeneratorFamilyData ctx realization)
  (assignment : LocGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).family = family := rfl

@[simp] theorem ofFamilyAndAssignment_assignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : LocGeneratorFamilyData ctx realization)
  (assignment : LocGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).assignment = assignment := rfl

end LocGeneratorRowSpinePiece

namespace NisGeneratorRowSpinePiece

def ofFamilyAndAssignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : NisGeneratorFamilyData ctx realization)
  (assignment : NisGeneratorRealizationAssignment ctx realization) :
  NisGeneratorRowSpinePiece ctx where
  realization := realization
  family := family
  assignment := assignment

@[simp] theorem ofFamilyAndAssignment_realization
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : NisGeneratorFamilyData ctx realization)
  (assignment : NisGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).realization = realization := rfl

@[simp] theorem ofFamilyAndAssignment_family
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : NisGeneratorFamilyData ctx realization)
  (assignment : NisGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).family = family := rfl

@[simp] theorem ofFamilyAndAssignment_assignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : NisGeneratorFamilyData ctx realization)
  (assignment : NisGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).assignment = assignment := rfl

end NisGeneratorRowSpinePiece

namespace A1GeneratorRowSpinePiece

def ofFamilyAndAssignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : A1GeneratorFamilyData ctx realization)
  (assignment : A1GeneratorRealizationAssignment ctx realization) :
  A1GeneratorRowSpinePiece ctx where
  realization := realization
  family := family
  assignment := assignment

@[simp] theorem ofFamilyAndAssignment_realization
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : A1GeneratorFamilyData ctx realization)
  (assignment : A1GeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).realization = realization := rfl

@[simp] theorem ofFamilyAndAssignment_family
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : A1GeneratorFamilyData ctx realization)
  (assignment : A1GeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).family = family := rfl

@[simp] theorem ofFamilyAndAssignment_assignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : A1GeneratorFamilyData ctx realization)
  (assignment : A1GeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).assignment = assignment := rfl

end A1GeneratorRowSpinePiece

namespace EnvGeneratorRowSpinePiece

def ofFamilyAndAssignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : EnvGeneratorFamilyData ctx realization)
  (assignment : EnvGeneratorRealizationAssignment ctx realization) :
  EnvGeneratorRowSpinePiece ctx where
  realization := realization
  family := family
  assignment := assignment

@[simp] theorem ofFamilyAndAssignment_realization
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : EnvGeneratorFamilyData ctx realization)
  (assignment : EnvGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).realization = realization := rfl

@[simp] theorem ofFamilyAndAssignment_family
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : EnvGeneratorFamilyData ctx realization)
  (assignment : EnvGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).family = family := rfl

@[simp] theorem ofFamilyAndAssignment_assignment
  {ctx : ClassicalComparisonContext.{u, v}}
  (realization : GeometricRealizationFunctorData ctx)
  (family : EnvGeneratorFamilyData ctx realization)
  (assignment : EnvGeneratorRealizationAssignment ctx realization) :
  (ofFamilyAndAssignment realization family assignment).assignment = assignment := rfl

end EnvGeneratorRowSpinePiece

end ClassicalPeriods
end TraceCalc
