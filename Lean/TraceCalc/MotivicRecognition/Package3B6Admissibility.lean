import TraceCalc.MotivicRecognition.Package3BProofs

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

namespace Package3B6

/-- Canonical `AdmissibleLocalizationAxioms` built from a `GeneratorRealizationAssignmentTable`.

Each sub-structure is the canonical sealed value from the corresponding `ofClassicalGeneratorRealization`
constructor in `Package3BProofs`:
- `Corr` = `CorrFunctorialityTarget.ofClassicalGeneratorRealization` (theoremTarget = `CorrPacketSoundnessFromGeneratorRealizationTarget`)
- `Loc`  = `OpenClosedLocalizationTarget.ofClassicalGeneratorRealization` (theoremTarget = Loc ∧ triangleCompat)
- `Nis`  = `NisnevichDescentTarget.ofClassicalGeneratorRealization`  (theoremTarget = Nis ∧ descentSquare)
- `A1`   = `A1InvarianceTarget.ofClassicalGeneratorRealization`      (theoremTarget = A1 ∧ framedExtraction)
- `Env`  = `EnvelopeExactnessTarget.ofClassicalGeneratorRealization` (theoremTarget = Env ∧ exactCompletion)

Required name for the Package 3B receipt index.
-/
def admissibleLocalizationAxioms_of_sealed_boundaries
    {trace : TracePresentation.{u, v, w, x, y}}
    (motivic : MotivicCategoryCandidate trace.base)
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    AdmissibleLocalizationAxioms trace motivic where
  Corr := CorrFunctorialityTarget.ofClassicalGeneratorRealization assignmentTable
  Loc  := OpenClosedLocalizationTarget.ofClassicalGeneratorRealization assignmentTable
  Nis  := NisnevichDescentTarget.ofClassicalGeneratorRealization assignmentTable
  A1   := A1InvarianceTarget.ofClassicalGeneratorRealization assignmentTable
  Env  := EnvelopeExactnessTarget.ofClassicalGeneratorRealization assignmentTable
  localizationFeedsRecognitionTarget :=
    ClassicalPeriods.CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable ∧
    (ClassicalPeriods.LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget) ∧
    (ClassicalPeriods.NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget) ∧
    (ClassicalPeriods.A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget) ∧
    (ClassicalPeriods.EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget)

/-- Composite recognition-feed proof from the five sealed Package 3B boundary
families.

This proves the final `localizationFeedsRecognitionTarget` field of the
canonical composite record, using exactly the named providers for Corr, Loc,
Nis, A¹, and Env.
-/
theorem localizationFeedsRecognition_holds
    {trace : TracePresentation.{u, v, w, x, y}}
    (motivic : MotivicCategoryCandidate trace.base)
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    (admissibleLocalizationAxioms_of_sealed_boundaries
      (trace := trace) motivic assignmentTable).localizationFeedsRecognitionTarget :=
  ⟨ corr_theorem_holds assignmentTable
  , ⟨ loc_theorem_holds assignmentTable
    , ⟨ nis_theorem_holds assignmentTable
      , ⟨ a1_theorem_holds assignmentTable
        , env_theorem_holds assignmentTable ⟩ ⟩ ⟩ ⟩

/-- Certified composite admissibility wrapper: the canonical admissibility
record plus proofs of every boundary theorem and the final recognition-feed
field.
-/
structure CertifiedAdmissibleLocalizationAxioms
    {trace : TracePresentation.{u, v, w, x, y}}
    (motivic : MotivicCategoryCandidate trace.base)
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) where
  target : AdmissibleLocalizationAxioms trace motivic :=
    admissibleLocalizationAxioms_of_sealed_boundaries motivic assignmentTable
  corr_holds : target.Corr.theoremTarget
  loc_holds : target.Loc.theoremTarget
  nis_holds : target.Nis.theoremTarget
  a1_holds : target.A1.theoremTarget
  env_holds : target.Env.theoremTarget
  env_exactness_holds : target.Env.exactnessTarget
  localizationFeedsRecognition_holds : target.localizationFeedsRecognitionTarget

/-- Build the certified composite admissibility wrapper from the five sealed
boundary families.
-/
def CertifiedAdmissibleLocalizationAxioms.ofSealedBoundaries
    {trace : TracePresentation.{u, v, w, x, y}}
    (motivic : MotivicCategoryCandidate trace.base)
    {ctx : ClassicalBridge.ClassicalComparisonContext.{u, v}}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable ctx) :
    CertifiedAdmissibleLocalizationAxioms (trace := trace) motivic assignmentTable where
  target := admissibleLocalizationAxioms_of_sealed_boundaries motivic assignmentTable
  corr_holds := TraceCalc.MotivicRecognition.corr_theorem_holds assignmentTable
  loc_holds := TraceCalc.MotivicRecognition.loc_theorem_holds assignmentTable
  nis_holds := TraceCalc.MotivicRecognition.nis_theorem_holds assignmentTable
  a1_holds := TraceCalc.MotivicRecognition.a1_theorem_holds assignmentTable
  env_holds := TraceCalc.MotivicRecognition.env_theorem_holds assignmentTable
  env_exactness_holds := TraceCalc.MotivicRecognition.env_exactness_holds assignmentTable
  localizationFeedsRecognition_holds :=
    Package3B6.localizationFeedsRecognition_holds motivic assignmentTable

/-- Proof of `ClassicalDMgmQPresentationTheorems` given that a presentation's
`admissibleLocalizationAxioms` equals the canonical sealed record built by
`admissibleLocalizationAxioms_of_sealed_boundaries`.

The six required fields follow directly from the five sealed boundary theorems
(Packages 3B0–3B5), bridged through Package3BProofs:
- `corr_holds`          ← `corr_theorem_holds`
- `loc_holds`           ← `loc_theorem_holds`
- `nis_holds`           ← `nis_theorem_holds`
- `a1_holds`            ← `a1_theorem_holds`
- `env_holds`           ← `env_theorem_holds`
- `env_exactness_holds` ← `env_exactness_holds`

Required name for the Package 3B receipt index.
-/
theorem classicalDMgmQPresentationTheorems_of_sealed_boundaries
    {trace : TracePresentation.{u, v, w, x, y}}
    {presentation : ClassicalMotivicPresentation trace}
    (assignmentTable : ClassicalPeriods.GeneratorRealizationAssignmentTable presentation.classicalContext)
    (h : presentation.admissibleLocalizationAxioms =
         admissibleLocalizationAxioms_of_sealed_boundaries
           presentation.motivicCategory assignmentTable) :
    ClassicalDMgmQPresentationTheorems presentation where
  corr_holds          := h ▸ corr_theorem_holds assignmentTable
  loc_holds           := h ▸ loc_theorem_holds assignmentTable
  nis_holds           := h ▸ nis_theorem_holds assignmentTable
  a1_holds            := h ▸ a1_theorem_holds assignmentTable
  env_holds           := h ▸ env_theorem_holds assignmentTable
  env_exactness_holds := h ▸ env_exactness_holds assignmentTable

end Package3B6

end MotivicRecognition
end TraceCalc
