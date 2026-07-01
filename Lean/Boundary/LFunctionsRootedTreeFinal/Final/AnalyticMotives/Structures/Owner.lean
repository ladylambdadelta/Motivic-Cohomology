import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.TStructure.Owner

/-!
# Structures on analytic motives

Weight and `t`-structure development is downstream from the stable analytic
category.  Weight comes from compactification strata and residue depth; the
`t`-structure is developed from the analytic truncation calculus in this lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The package of additional structures on stable analytic motives: geometric
weight data and internally developed analytic motivic `t`-structure data.
-/
structure AnalyticMotiveStructures where
  stablePackage : StableAnalyticMotivePackage
  weight : AnalyticWeightStructureData
  tStructure : AnalyticMotivicTStructureData
  weight_stablePackage_eq :
    weight.geometric.stablePackage = stablePackage
  tStructure_stablePackage_eq :
    tStructure.stablePackage = stablePackage

namespace AnalyticMotiveStructures

/-- The geometric weight data in the structure package. -/
def weightData (S : AnalyticMotiveStructures) :
    AnalyticWeightStructureData :=
  S.weight

/--
The analytic weight data is attached to the same stable package as the
surrounding structure package.
-/
theorem weight_stablePackage_compatibility
    (S : AnalyticMotiveStructures) :
    S.weight.geometric.stablePackage = S.stablePackage :=
  S.weight_stablePackage_eq

/-- The analytic motivic `t`-structure data in the structure package. -/
def tStructureData (S : AnalyticMotiveStructures) :
    AnalyticMotivicTStructureData :=
  S.tStructure

/--
The analytic motivic `t`-structure data is attached to the same stable package
as the surrounding structure package.
-/
theorem tStructure_stablePackage_compatibility
    (S : AnalyticMotiveStructures) :
    S.tStructure.stablePackage = S.stablePackage :=
  S.tStructure_stablePackage_eq

/--
The compact-geometric closed object seen by the `t`-structure package agrees
with the compact-geometric closed object of the surrounding stable package.
-/
theorem tStructure_closedObject_compatibility
    (S : AnalyticMotiveStructures) :
    S.tStructure.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      S.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject :=
  congrArg
    (fun P =>
      P.compactLayer.compactGeometric.thickClosure.closedObject)
    S.tStructure_stablePackage_eq

/--
The compact-geometric closed object seen by the weight package agrees with the
compact-geometric closed object of the surrounding stable package.
-/
theorem weight_closedObject_compatibility
    (S : AnalyticMotiveStructures) :
    S.weight.geometric.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      S.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject :=
  congrArg
    (fun P =>
      P.compactLayer.compactGeometric.thickClosure.closedObject)
    S.weight_stablePackage_eq

end AnalyticMotiveStructures

/--
Downstream trace compatibility for the weight component of an analytic motive
structure package.  This keeps trace positivity attached as evidence rather
than as part of the geometric weight definition.
-/
structure AnalyticMotiveStructuresTraceCompatibility
    (S : AnalyticMotiveStructures) where
  weightTrace :
    AnalyticWeightTraceCompatibilityData S.weight

namespace AnalyticMotiveStructuresTraceCompatibility

/-- Trace compatibility data for the structure package's weight component. -/
def weightTraceData {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S) :
    AnalyticWeightTraceCompatibilityData S.weight :=
  C.weightTrace

/-- Boundary-stream compatibility at a weight index in the structure package. -/
def boundaryAt {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryStreamWeightCompatibility
      S.weight.geometric.weightCandidate i :=
  C.weightTrace.boundaryAt i

/-- Packet/Hilbert compatibility at a weight index in the structure package. -/
def packetHilbertAt {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    PacketHilbertWeightCompatibility (C.boundaryAt i) :=
  C.weightTrace.packetHilbertAt i

/-- The boundary presentation at an index is attached to the selected weight stratum bulk. -/
theorem boundary_bulk_eq {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    (C.boundaryAt i).boundaryPresentation.bulk =
      S.weight.bulkAt i :=
  AnalyticWeightTraceCompatibilityData.boundary_bulk_eq
    C.weightTrace i

/-- The boundary stream at an index lies in the positive cone. -/
theorem boundary_stream_mem_positiveCone
    {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.InPositiveCone
      (C.boundaryAt i).stream :=
  AnalyticWeightTraceCompatibilityData.boundary_stream_mem_positiveCone
    C.weightTrace i

/-- The packet norm square at an index is nonnegative. -/
theorem packet_normSq_nonnegative
    {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).normSq :=
  AnalyticWeightTraceCompatibilityData.packet_normSq_nonnegative
    C.weightTrace i

/-- The Hilbert/GNS scalar at an index is nonnegative. -/
theorem hilbert_scalar_nonnegative
    {S : AnalyticMotiveStructures}
    (C : AnalyticMotiveStructuresTraceCompatibility S)
    (i : S.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).hilbertPresentation.gnsScalar :=
  AnalyticWeightTraceCompatibilityData.hilbert_scalar_nonnegative
    C.weightTrace i

end AnalyticMotiveStructuresTraceCompatibility

end AnalyticMotives
end LFunctions
end Boundary
