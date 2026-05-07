import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.ClassicalPeriods.GeometricPeriodSpine
import TraceCalc.ClassicalPeriods.SymbolicGeneratorExamples

universe u v w

namespace TraceCalc
namespace ClassicalPeriods

/-- Compact proof-discharge index for the current ClassicalPeriods surface.

This file is intentionally read-only in spirit: it records which API layers already have usable
constructors/projections so future bots can stop extending the generator surface unless this index
exposes a genuinely missing projection. -/
namespace ClassicalProofDischargeIndex

/-- Closed theorem-target layer exported by `PeriodConjectureTarget.lean`. -/
namespace TargetLayer

abbrev BaseFaithfulnessTarget := PeriodConjectureTargetIndex.BaseFaithfulnessTarget
abbrev FramedFaithfulnessTarget := PeriodConjectureTargetIndex.FramedFaithfulnessTarget
abbrev ReflectionCore := PeriodConjectureTargetIndex.ReflectionCore
abbrev FaithfulnessDecomposition := PeriodConjectureTargetIndex.FaithfulnessDecomposition
abbrev ReverseMathObligations := PeriodConjectureTargetIndex.ReverseMathObligations
abbrev BaseFaithfulnessStatement := PeriodConjectureTargetIndex.BaseFaithfulnessStatement
abbrev FramedFaithfulnessStatement := PeriodConjectureTargetIndex.FramedFaithfulnessStatement

theorem baseFaithfulness_of_reflection
    (target : BaseFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.baseFaithfulness_of_reflection target

theorem framedFaithfulness_of_reflection
    (target : FramedFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.framedFaithfulness_of_reflection target

end TargetLayer

/-- Geometric object/realization layer already discharged to a stable API surface. -/
namespace GeometricObjectRealizationLayer

abbrev PeriodObject := GeometricPeriodObject
abbrev Correspondence := GeometricCorrespondence
abbrev FramedObject := GeometricFramedObject
abbrev BettiRealizationData := GeometricBettiRealizationData
abbrev DeRhamRealizationData := GeometricDeRhamRealizationData
abbrev ComparisonData := GrothendieckComparisonData
abbrev RealizationFunctor := GeometricRealizationFunctorData
abbrev FramedPeriodData := GeometricFramedPeriodData
abbrev TomographySoundness := GeometricRealizationTomographySoundness
abbrev ToConcreteTomographyPackage :=
  GeometricRealizationTomographySoundness.toConcreteRealizationTomographyPackage

end GeometricObjectRealizationLayer

/-- Generator-family and assignment-table layer already discharged to stable constructors and
forgetful projections. -/
namespace GeneratorLayer

abbrev CorrFamily := CorrGeneratorFamilyData
abbrev LocFamily := LocGeneratorFamilyData
abbrev NisFamily := NisGeneratorFamilyData
abbrev A1Family := A1GeneratorFamilyData
abbrev EnvFamily := EnvGeneratorFamilyData
abbrev FamilyPackage := GeometricGeneratorFamilyPackage
abbrev AssignmentTable := GeneratorRealizationAssignmentTable
abbrev BuildFamilyPackage := GeometricGeneratorFamilyPackage.ofRows
abbrev BuildAssignmentTable := GeneratorRealizationAssignmentTable.ofAssignments
abbrev ToFamilyPackage := GeneratorRealizationAssignmentTable.toGeometricGeneratorFamilyPackage
abbrev ToLocalizationPackage := GeneratorRealizationAssignmentTable.toGeometricLocalizationPackage
abbrev ToReadiness := GeneratorRealizationAssignmentTable.toClassicalMotivicRealizationReadiness

end GeneratorLayer

/-- Unit sanity model index.

The unit generator-example chain currently lives outside the minimal green import path of this
index file, so the index records its representative names textually rather than re-importing the
older unit-example dependency chain here. -/
namespace UnitSanityModel

/-- Representative unit-example names already closed elsewhere in the ClassicalPeriods lane. -/
def representativeLeanNames : List String :=
  [ "unitGeneratorRealizationAssignmentTable"
  , "unitGeometricGeneratorFamilyPackage"
  , "unitGeometricLocalizationPackageFromAssignmentTable"
  , "unitAssignmentTableClassicalMotivicRealizationReadiness"
  ]

end UnitSanityModel

/-- Symbolic one-row examples already closed for all manuscript generator families. -/
namespace SymbolicRows

abbrev CorrDatum := SymbolicCorrDatum
abbrev CorrFamily := symbolicCorrGeneratorFamilyData
abbrev CorrAssignment := symbolicCorrGeneratorRealizationAssignment
abbrev LocDatum := SymbolicLocDatum
abbrev LocFamily := symbolicLocGeneratorFamilyData
abbrev LocAssignment := symbolicLocGeneratorRealizationAssignment
abbrev NisDatum := SymbolicNisDatum
abbrev NisFamily := symbolicNisGeneratorFamilyData
abbrev NisAssignment := symbolicNisGeneratorRealizationAssignment
abbrev A1Datum := SymbolicA1Datum
abbrev A1Family := symbolicA1GeneratorFamilyData
abbrev A1Assignment := symbolicA1GeneratorRealizationAssignment
abbrev EnvDatum := SymbolicEnvDatum
abbrev EnvFamily := symbolicEnvGeneratorFamilyData
abbrev EnvAssignment := symbolicEnvGeneratorRealizationAssignment

theorem corr_sourceObject
    {ctx : ClassicalComparisonContext.{u, v}} (datum : CorrDatum ctx) :
    (CorrFamily datum).sourceObject PUnit.unit = datum.source :=
  symbolicCorrGeneratorFamilyData_sourceObject datum

theorem loc_ambientObject
    {ctx : ClassicalComparisonContext.{u, v}} (datum : LocDatum ctx) :
    (LocFamily datum).ambientObject PUnit.unit = datum.ambient :=
  symbolicLocGeneratorFamilyData_ambientObject datum

theorem nis_baseObject
    {ctx : ClassicalComparisonContext.{u, v}} (datum : NisDatum ctx) :
    (NisFamily datum).baseObject PUnit.unit = datum.base :=
  symbolicNisGeneratorFamilyData_baseObject datum

theorem a1_baseObject
    {ctx : ClassicalComparisonContext.{u, v}} (datum : A1Datum ctx) :
    (A1Family datum).baseObject PUnit.unit = datum.base :=
  symbolicA1GeneratorFamilyData_baseObject datum

theorem env_envelopeCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}} (datum : EnvDatum ctx) :
    (EnvFamily datum).envelopeCorrespondence PUnit.unit = datum.envelopeCorrespondence :=
  symbolicEnvGeneratorFamilyData_envelopeCorrespondence datum

end SymbolicRows

/-- Readable dependency-spine wrappers already closed as convenience packaging only. -/
namespace SpineWrappers

abbrev Spine := GeometricPeriodSpine
abbrev BuildSpine := GeneratorRealizationAssignmentTable.toGeometricPeriodSpine
abbrev CorrRowPiece := CorrGeneratorRowSpinePiece
abbrev LocRowPiece := LocGeneratorRowSpinePiece
abbrev NisRowPiece := NisGeneratorRowSpinePiece
abbrev A1RowPiece := A1GeneratorRowSpinePiece
abbrev EnvRowPiece := EnvGeneratorRowSpinePiece
abbrev BuildCorrRowPiece := CorrGeneratorRowSpinePiece.ofFamilyAndAssignment
abbrev BuildLocRowPiece := LocGeneratorRowSpinePiece.ofFamilyAndAssignment
abbrev BuildNisRowPiece := NisGeneratorRowSpinePiece.ofFamilyAndAssignment
abbrev BuildA1RowPiece := A1GeneratorRowSpinePiece.ofFamilyAndAssignment
abbrev BuildEnvRowPiece := EnvGeneratorRowSpinePiece.ofFamilyAndAssignment

end SpineWrappers

/-- Remaining hard theorem nodes for the ClassicalPeriods lane.

Anything listed here should be treated as mathematically open in this lane even if the surrounding
API is already proof-discharged. -/
inductive RemainingHardNode
  | correspondenceFunctoriality
  | openClosedLocalization
  | nisnevichDescent
  | a1Invariance
  | envelopeExactness
  | bettiDeRhamComparisonRealization
  | scalarFramedExtraction
deriving DecidableEq, Repr

namespace RemainingHardNode

abbrev CorrespondenceFunctorialitySurface := GeometricCorrespondenceFunctorialityTarget
abbrev OpenClosedLocalizationSurface := GeometricOpenClosedLocalizationTarget
abbrev NisnevichDescentSurface := GeometricNisnevichDescentTarget
abbrev A1InvarianceSurface := GeometricA1InvarianceTarget
abbrev EnvelopeExactnessSurface := GeometricEnvelopeExactnessTarget
abbrev BettiRealizationSurface := GeometricBettiRealizationData
abbrev DeRhamRealizationSurface := GeometricDeRhamRealizationData
abbrev ComparisonRealizationSurface := GrothendieckComparisonData
abbrev FramedExtractionSurface := GeometricFramedPeriodFunctoriality
abbrev ScalarExtractionSurface := GeometricPeriodsRealizeConcreteFramedData

/-- Human-readable label for docs and future triage. -/
def label : RemainingHardNode → String
  | .correspondenceFunctoriality => "real correspondence functoriality"
  | .openClosedLocalization => "real open/closed localization"
  | .nisnevichDescent => "real Nisnevich descent"
  | .a1Invariance => "real A1 invariance"
  | .envelopeExactness => "real envelope exactness"
  | .bettiDeRhamComparisonRealization => "real Betti/de Rham comparison realization"
  | .scalarFramedExtraction => "real scalar/framed extraction from geometry"

/-- Representative Lean entry point for the hard node. -/
def representativeLeanName : RemainingHardNode → String
  | .correspondenceFunctoriality => "GeometricCorrespondenceFunctorialityTarget"
  | .openClosedLocalization => "GeometricOpenClosedLocalizationTarget"
  | .nisnevichDescent => "GeometricNisnevichDescentTarget"
  | .a1Invariance => "GeometricA1InvarianceTarget"
  | .envelopeExactness => "GeometricEnvelopeExactnessTarget"
  | .bettiDeRhamComparisonRealization =>
      "GeometricBettiRealizationData / GeometricDeRhamRealizationData / GrothendieckComparisonData"
  | .scalarFramedExtraction =>
      "GeometricFramedPeriodFunctoriality / GeometricPeriodsRealizeConcreteFramedData"

/-- Canonical list of still-hard classical nodes. -/
def all : List RemainingHardNode :=
  [ .correspondenceFunctoriality
  , .openClosedLocalization
  , .nisnevichDescent
  , .a1Invariance
  , .envelopeExactness
  , .bettiDeRhamComparisonRealization
  , .scalarFramedExtraction
  ]

end RemainingHardNode

end ClassicalProofDischargeIndex

end ClassicalPeriods
end TraceCalc