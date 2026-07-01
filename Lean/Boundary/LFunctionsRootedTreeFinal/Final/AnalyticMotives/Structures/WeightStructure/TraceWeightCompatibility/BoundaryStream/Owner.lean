import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.BoundaryStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Candidate.Owner

/-!
# Boundary-stream compatibility for geometric weights

This file owns compatibility between geometric-contour weight data and boundary
trace streams.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Compatibility between a geometric weight stratum and a realized boundary trace
stream.  The geometric side supplies the bulk and stratum; the trace side
supplies positive-cone and stream-transport properties.
-/
structure BoundaryStreamWeightCompatibility
    {S : AnalyticMotivicStableInfinityInterface}
    (W : GeometricWeightCandidate S)
    (i : W.StratumIndex) where
  boundaryPresentation : BoundaryStreamPresentation
  bulk_eq :
    boundaryPresentation.bulk = W.bulkAt i
  stream_positive :
    BoundaryTraceStream.InPositiveCone
      boundaryPresentation.stream
  squareRepresentatives :
    BoundaryTraceStream.HasSquareRepresentatives
      boundaryPresentation.stream
  lowerWeightAbsorption :
    BoundaryTraceStream.HasLowerWeightAbsorption
      boundaryPresentation.stream

namespace BoundaryStreamWeightCompatibility

/-- The boundary-stream presentation used in compatibility data. -/
def presentation {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    BoundaryStreamPresentation :=
  C.boundaryPresentation

/-- The compatible boundary stream. -/
def stream {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    BoundaryTraceStream :=
  C.boundaryPresentation.stream

/-- The compatible trace packet. -/
def packet {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    ZetaAdmissibleFunction :=
  C.boundaryPresentation.packet

/-- The trace presentation is attached to the stratum bulk. -/
theorem presentation_bulk_eq {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    C.boundaryPresentation.bulk = W.bulkAt i :=
  C.bulk_eq

/-- The compatible boundary stream lies in the positive cone. -/
theorem stream_mem_positiveCone {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    BoundaryTraceStream.InPositiveCone C.stream :=
  C.stream_positive

/-- The compatible boundary stream has square representatives. -/
theorem stream_hasSquareRepresentatives {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    BoundaryTraceStream.HasSquareRepresentatives C.stream :=
  C.squareRepresentatives

/-- The compatible boundary stream has lower-weight absorption. -/
theorem stream_hasLowerWeightAbsorption {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    BoundaryTraceStream.HasLowerWeightAbsorption C.stream :=
  C.lowerWeightAbsorption

/-- The compatible stream agrees with the owner boundary trace stream. -/
theorem stream_eq_owner {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (C : BoundaryStreamWeightCompatibility W i) :
    C.stream = boundaryTraceStream C.packet :=
  BoundaryStreamPresentation.realizedStream_eq
    C.boundaryPresentation

end BoundaryStreamWeightCompatibility

end AnalyticMotives
end LFunctions
end Boundary
