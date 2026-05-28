import TraceCalc.ClassicalPeriods.Package3BGeneratorSoundness

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

namespace Package3B5

/-- Env: envelope-functoriality comparison agreement from certified envelope replay data.

The envelope exactness comparison holds because the trace-native certified envelope
replay data (`CertifiedEnvReplayData`) witnesses the comparison agreement across all
envelope generator indices.
Required name for the Package 3B receipt index.
-/
theorem env_envelopeFunctoriality_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  envComparisonAgreement_from_certifiedReplay assignmentTable

/-- Env: exactness / formal-closure soundness from certified envelope replay data.

The envelope exactness (formal closure target) holds because the trace-native certified
envelope replay data witnesses it.
Required name for the Package 3B receipt index.
-/
theorem env_exactness_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.envAssignment.exactCompletionTarget :=
  envFormalClosureSoundness_from_certifiedReplay assignmentTable

/-- Env: bundled theorem target from certified envelope replay data.

Packages both the comparison soundness and formal-closure exactness.
Required name for the Package 3B receipt index.
-/
theorem env_theoremTarget_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget :=
  envPacketSoundnessFromGeneratorRealization assignmentTable

end Package3B5

end ClassicalPeriods
end TraceCalc
