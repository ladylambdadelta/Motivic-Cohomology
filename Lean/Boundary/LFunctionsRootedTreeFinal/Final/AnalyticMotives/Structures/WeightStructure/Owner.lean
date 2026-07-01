import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.GeometricWeight.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.ContourGeneration.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.TraceWeightCompatibility.Owner

/-!
# Weight structure for analytic motives

The analytic weight structure is geometric-contour data: compactification
strata, boundary depth, residue filtration, and generator closure.  Trace
positivity and packet nonnegativity are compatibility checks through
realization, not the definition of weight.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Analytic weight-structure data.  The defining component is geometric-contour
weight data; trace compatibility is a downstream realization check.
-/
structure AnalyticWeightStructureData where
  geometric : GeometricContourWeightData

namespace AnalyticWeightStructureData

/-- The geometric-contour component of analytic weight data. -/
def geometricData (W : AnalyticWeightStructureData) :
    GeometricContourWeightData :=
  W.geometric

/-- The stable package carrying analytic weight data. -/
def stable (W : AnalyticWeightStructureData) :
    StableAnalyticMotivePackage :=
  W.geometric.stablePackage

/-- The geometric weight candidate in analytic weight data. -/
def candidate (W : AnalyticWeightStructureData) :
    GeometricWeightCandidate W.geometric.stablePackage.infinityInterface :=
  W.geometric.weightCandidate

/-- The stratum selected by an analytic weight index. -/
def stratumAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    GeometricWeightStratum W.geometric.stablePackage.infinityInterface :=
  W.geometric.stratumAt i

/-- The stable object selected by an analytic weight index. -/
def objectAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    W.geometric.stablePackage.infinityInterface.Object :=
  W.geometric.objectAt i

/-- The contour-admissible bulk selected by an analytic weight index. -/
def bulkAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    ContourAdmissibleBulk :=
  W.geometric.bulkAt i

/-- The boundary face selected by an analytic weight index. -/
def faceAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    AnalyticBoundaryFace (W.bulkAt i).boundary.compactification :=
  W.geometric.faceAt i

/-- The residue depth selected by an analytic weight index. -/
def depthAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    Nat :=
  W.geometric.depthAt i

/-- The residue-depth filtration selected by an analytic weight index. -/
def filtrationAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    AnalyticResidueFiltration (W.bulkAt i).boundary :=
  W.geometric.filtrationAt i

/-- The selected residue depth agrees with the selected residue filtration. -/
theorem depth_eq_filtrationAt (W : AnalyticWeightStructureData)
    (i : W.geometric.weightCandidate.StratumIndex) :
    W.depthAt i =
      (W.filtrationAt i).depth (W.stratumAt i).faceIndex :=
  GeometricContourWeightData.depth_eq_filtrationAt W.geometric i

/-- Membership in the lower-weight class of analytic weight data. -/
def inLowerWeight (W : AnalyticWeightStructureData)
    (n : Int) (X : W.geometric.stablePackage.infinityInterface.Object) :
    Type :=
  W.geometric.inLowerWeight n X

/-- Membership in the upper-weight class of analytic weight data. -/
def inUpperWeight (W : AnalyticWeightStructureData)
    (n : Int) (X : W.geometric.stablePackage.infinityInterface.Object) :
    Type :=
  W.geometric.inUpperWeight n X

end AnalyticWeightStructureData

/--
Downstream trace-realization compatibility for analytic weight data.  The
weight data itself remains geometric; this package records boundary-stream and
packet/Hilbert positivity evidence for its geometric strata.
-/
structure AnalyticWeightTraceCompatibilityData
    (W : AnalyticWeightStructureData) where
  traceCompatibility :
    TraceWeightCompatibilityData W.geometric

namespace AnalyticWeightTraceCompatibilityData

/-- The trace compatibility package attached to analytic weight data. -/
def trace {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W) :
    TraceWeightCompatibilityData W.geometric :=
  C.traceCompatibility

/-- Boundary-stream compatibility at an analytic weight index. -/
def boundaryAt {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    BoundaryStreamWeightCompatibility W.geometric.weightCandidate i :=
  C.traceCompatibility.boundaryAt i

/-- Packet/Hilbert positivity compatibility at an analytic weight index. -/
def packetHilbertAt {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    PacketHilbertWeightCompatibility (C.boundaryAt i) :=
  C.traceCompatibility.packetHilbertAt i

/-- The boundary presentation at an index is attached to the analytic weight stratum bulk. -/
theorem boundary_bulk_eq {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    (C.boundaryAt i).boundaryPresentation.bulk =
      W.bulkAt i :=
  TraceWeightCompatibilityData.boundary_bulk_eq
    C.traceCompatibility i

/-- The boundary stream at an index lies in the positive cone. -/
theorem boundary_stream_mem_positiveCone
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.InPositiveCone
      (C.boundaryAt i).stream :=
  TraceWeightCompatibilityData.boundary_stream_mem_positiveCone
    C.traceCompatibility i

/-- The boundary stream at an index has square representatives. -/
theorem boundary_stream_hasSquareRepresentatives
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.HasSquareRepresentatives
      (C.boundaryAt i).stream :=
  TraceWeightCompatibilityData.boundary_stream_hasSquareRepresentatives
    C.traceCompatibility i

/-- The boundary stream at an index has lower-weight absorption. -/
theorem boundary_stream_hasLowerWeightAbsorption
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.HasLowerWeightAbsorption
      (C.boundaryAt i).stream :=
  TraceWeightCompatibilityData.boundary_stream_hasLowerWeightAbsorption
    C.traceCompatibility i

/-- The packet norm square at an index is nonnegative. -/
theorem packet_normSq_nonnegative
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).normSq :=
  TraceWeightCompatibilityData.packet_normSq_nonnegative
    C.traceCompatibility i

/-- The Hilbert/GNS scalar at an index is nonnegative. -/
theorem hilbert_scalar_nonnegative
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).hilbertPresentation.gnsScalar :=
  TraceWeightCompatibilityData.hilbert_scalar_nonnegative
    C.traceCompatibility i

/-- The packet norm square at an index agrees with the owner packet norm. -/
theorem packet_normSq_eq_owner
    {W : AnalyticWeightStructureData}
    (C : AnalyticWeightTraceCompatibilityData W)
    (i : W.geometric.weightCandidate.StratumIndex) :
    (C.packetHilbertAt i).normSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        (C.boundaryAt i).packet 0 :=
  TraceWeightCompatibilityData.packet_normSq_eq_owner
    C.traceCompatibility i

end AnalyticWeightTraceCompatibilityData

end AnalyticMotives
end LFunctions
end Boundary
