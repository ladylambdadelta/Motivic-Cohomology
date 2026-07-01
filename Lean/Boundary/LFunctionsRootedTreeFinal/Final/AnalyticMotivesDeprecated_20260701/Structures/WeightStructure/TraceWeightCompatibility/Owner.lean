import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.TraceWeightCompatibility.BoundaryStream.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.TraceWeightCompatibility.PacketPositivity.Owner

/-!
# Trace compatibility for geometric weights

This file owns compatibility between geometric-contour weights and the trace
realization surfaces: boundary streams, packet norms, and Hilbert/GNS scalars.
Trace positivity is evidence for compatibility, not the definition of weight.

Dependency order: boundary-stream compatibility, then packet/Hilbert positivity
compatibility.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Trace compatibility data for a geometric-contour weight candidate.  This
packages boundary-stream compatibility and packet/Hilbert positivity for each
geometric weight stratum.
-/
structure TraceWeightCompatibilityData
    (W : GeometricContourWeightData) where
  boundaryCompatibility :
    (i : W.weightCandidate.StratumIndex) →
      BoundaryStreamWeightCompatibility W.weightCandidate i
  packetHilbertCompatibility :
    (i : W.weightCandidate.StratumIndex) →
      PacketHilbertWeightCompatibility
        (boundaryCompatibility i)

namespace TraceWeightCompatibilityData

/-- Boundary-stream compatibility at a geometric weight index. -/
def boundaryAt {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    BoundaryStreamWeightCompatibility W.weightCandidate i :=
  C.boundaryCompatibility i

/-- Packet/Hilbert positivity compatibility at a geometric weight index. -/
def packetHilbertAt {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    PacketHilbertWeightCompatibility (C.boundaryAt i) :=
  C.packetHilbertCompatibility i

/-- The boundary presentation at an index is attached to the geometric stratum bulk. -/
theorem boundary_bulk_eq {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    (C.boundaryAt i).boundaryPresentation.bulk =
      W.bulkAt i :=
  BoundaryStreamWeightCompatibility.presentation_bulk_eq
    (C.boundaryAt i)

/-- The boundary stream at an index lies in the positive cone. -/
theorem boundary_stream_mem_positiveCone {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    BoundaryTraceStream.InPositiveCone
      (C.boundaryAt i).stream :=
  BoundaryStreamWeightCompatibility.stream_mem_positiveCone
    (C.boundaryAt i)

/-- The boundary stream at an index has square representatives. -/
theorem boundary_stream_hasSquareRepresentatives
    {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    BoundaryTraceStream.HasSquareRepresentatives
      (C.boundaryAt i).stream :=
  BoundaryStreamWeightCompatibility.stream_hasSquareRepresentatives
    (C.boundaryAt i)

/-- The boundary stream at an index has lower-weight absorption. -/
theorem boundary_stream_hasLowerWeightAbsorption
    {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    BoundaryTraceStream.HasLowerWeightAbsorption
      (C.boundaryAt i).stream :=
  BoundaryStreamWeightCompatibility.stream_hasLowerWeightAbsorption
    (C.boundaryAt i)

/-- The packet norm square at an index is nonnegative. -/
theorem packet_normSq_nonnegative {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).normSq :=
  PacketHilbertWeightCompatibility.normSq_nonnegative
    (C.packetHilbertAt i)

/-- The Hilbert/GNS scalar at an index is nonnegative. -/
theorem hilbert_scalar_nonnegative {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).hilbertPresentation.gnsScalar :=
  PacketHilbertWeightCompatibility.hilbertScalar_nonnegative
    (C.packetHilbertAt i)

/-- The packet norm square at an index agrees with the owner packet norm. -/
theorem packet_normSq_eq_owner {W : GeometricContourWeightData}
    (C : TraceWeightCompatibilityData W)
    (i : W.weightCandidate.StratumIndex) :
    (C.packetHilbertAt i).normSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        (C.boundaryAt i).packet 0 :=
  PacketHilbertWeightCompatibility.normSq_eq_owner
    (C.packetHilbertAt i)

end TraceWeightCompatibilityData

end AnalyticMotives
end LFunctions
end Boundary
