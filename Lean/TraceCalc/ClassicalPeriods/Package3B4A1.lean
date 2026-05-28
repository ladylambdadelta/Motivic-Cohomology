import TraceCalc.ClassicalPeriods.Package3BGeneratorSoundness

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

namespace Package3B4

/-- A¹: interval-object endpoint agreement from certified homotopy replay data.

The A¹-invariance interval-object comparison holds because the trace-native certified
homotopy replay data (`CertifiedA1HomotopyReplayData`) witnesses it.
Required name for the Package 3B receipt index.
-/
theorem a1_intervalObject_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  a1EndpointAgreement_from_certifiedReplay assignmentTable

/-- A¹: homotopy invariance / framed-extraction target from certified homotopy replay data.

The A¹-homotopy invariance holds because the trace-native certified homotopy replay
data witnesses it.
Required name for the Package 3B receipt index.
-/
theorem a1_homotopyInvariance_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.a1Assignment.framedExtractionTarget :=
  a1HomotopyInvariance_from_certifiedReplay assignmentTable

/-- A¹: bundled theorem target from certified homotopy replay data.

Packages both the comparison soundness and framed-extraction invariance.
Required name for the Package 3B receipt index.
-/
theorem a1_theoremTarget_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget :=
  a1PacketSoundnessFromGeneratorRealization assignmentTable

end Package3B4

end ClassicalPeriods
end TraceCalc
