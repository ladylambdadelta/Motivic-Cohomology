import TraceCalc.ClassicalPeriods.Package3BGeneratorSoundness

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

namespace Package3B2

/-- Loc: localization triangle compatibility from certified replay data.

The open/closed localization triangle holds because the trace-native certified
cone peel data (`CertifiedLocPacketReplayData`) witnesses the triangle.
Required name for the Package 3B receipt index.
-/
theorem loc_localizationTriangle_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.triangleCompatibilityTarget :=
  locTriangleCompatibility_from_certifiedReplay assignmentTable

/-- Loc: gluing / connecting-morphism compatibility from certified replay data.

The cone naturality connecting-morphism compatibility holds because the
trace-native certified cone peel data witnesses it.
Required name for the Package 3B receipt index.
-/
theorem loc_gluingCompatibility_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  locConnectingPacket_comparison_naturality_from_replay assignmentTable

/-- Loc: bundled theorem target from certified replay data.

Packages both the period-compatibility and triangle-compatibility parts.
Required name for the Package 3B receipt index.
-/
theorem loc_theoremTarget_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget :=
  locPacketSoundnessFromGeneratorRealization assignmentTable

end Package3B2

end ClassicalPeriods
end TraceCalc
