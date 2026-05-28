import TraceCalc.ClassicalPeriods.Package3BGeneratorSoundness

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

namespace Package3B3

/-- Nis: cover descent / overlap agreement from certified patch replay data.

The Nisnevich cover descent (overlap comparison between patches) holds because the
trace-native certified patch replay data (`CertifiedNisPatchReplayData`) witnesses it.
Required name for the Package 3B receipt index.
-/
theorem nis_coverDescent_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  nisOverlapAgreement_from_certifiedReplay assignmentTable

/-- Nis: hyperdescent / descent-square compatibility from certified patch replay data.

The Nisnevich descent square compatibility holds because the trace-native certified
patch replay data witnesses it.
Required name for the Package 3B receipt index.
-/
theorem nis_hyperdescent_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.nisAssignment.descentSquareCompatibilityTarget :=
  nisDescentSquareCompatibility_from_certifiedReplay assignmentTable

/-- Nis: bundled theorem target from certified patch replay data.

Packages both the comparison soundness and descent-square compatibility.
Required name for the Package 3B receipt index.
-/
theorem nis_theoremTarget_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget :=
  nisPacketSoundnessFromGeneratorRealization assignmentTable

end Package3B3

end ClassicalPeriods
end TraceCalc
