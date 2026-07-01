import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Owner

/-!
# Analytic motives lane

This off-critical-path lane separates bulk analytic contour motives from their
trace surfaces.  Bulk objects and contour-compatible correspondences are
upstream; boundary streams, vertical channels, packet comparisons, and
Hilbert/GNS data are downstream realization surfaces.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Top-level package for the analytic motives lane.  The bulk/stable/structure
components define the analytic-contour motive side; trace realization and
`DM_gm(ℚ)_ℚ` comparison are downstream surfaces.
-/
structure AnalyticMotivesLanePackage where
  stablePackage : StableAnalyticMotivePackage
  structures : AnalyticMotiveStructures
  traceRealization : AnalyticTraceRealization
  comparison : DMgmQQComparisonPackage
  structures_stablePackage_eq :
    structures.stablePackage = stablePackage
  comparison_stablePackage_eq :
    comparison.stableCoherence.stablePackage = stablePackage

namespace AnalyticMotivesLanePackage

/-- The stable analytic motive package in the lane. -/
def stable (P : AnalyticMotivesLanePackage) :
    StableAnalyticMotivePackage :=
  P.stablePackage

/-- The structure package in the analytic motives lane. -/
def structureData (P : AnalyticMotivesLanePackage) :
    AnalyticMotiveStructures :=
  P.structures

/--
The structure package in the analytic motives lane is attached to the lane's
stable package.
-/
theorem structures_stablePackage_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.stablePackage = P.stablePackage :=
  P.structures_stablePackage_eq

/--
The comparison package in the analytic motives lane is attached to the lane's
stable package.
-/
theorem comparison_stablePackage_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.comparison.stableCoherence.stablePackage = P.stablePackage :=
  P.comparison_stablePackage_eq

/--
The weight-triangular comparison structures are attached to the lane's stable
package.
-/
theorem comparison_weightTriangular_stablePackage_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.comparison.weightTriangular.analyticStructures.stablePackage =
      P.stablePackage :=
  Eq.trans P.comparison.weightTriangular_stablePackage_eq
    P.comparison_stablePackage_eq

/--
The lane's compact-geometric closed object agrees with the analytic Tate
stabilization used by its `DM_gm(ℚ)_ℚ` comparison.
-/
theorem compactGeometric_closedObject_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.comparison.tateComparison.analyticStabilization :=
  Eq.trans
    (congrArg
      (fun S =>
        S.compactLayer.compactGeometric.thickClosure.closedObject)
      (Eq.symm P.comparison_stablePackage_eq))
    (DMgmQQComparisonPackage.compactGeometric_closedObject_compatibility
      P.comparison)

/--
The structure package's compact-geometric closed object agrees with the
analytic Tate stabilization used by the lane's comparison package.
-/
theorem structures_closedObject_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.comparison.tateComparison.analyticStabilization :=
  Eq.trans
    (congrArg
      (fun S =>
        S.compactLayer.compactGeometric.thickClosure.closedObject)
      P.structures_stablePackage_eq)
    (compactGeometric_closedObject_compatibility P)

/--
The weight data in the lane's structure package is attached to the lane's
stable package.
-/
theorem weight_stablePackage_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.weight.geometric.stablePackage = P.stablePackage :=
  Eq.trans P.structures.weight_stablePackage_eq
    P.structures_stablePackage_eq

/--
The compact-geometric closed object seen by the lane's weight data agrees with
the analytic Tate stabilization used by the lane's comparison package.
-/
theorem weight_closedObject_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.weight.geometric.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.comparison.tateComparison.analyticStabilization :=
  Eq.trans
    (AnalyticMotiveStructures.weight_closedObject_compatibility
      P.structures)
    (structures_closedObject_compatibility P)

/--
The `t`-structure data in the lane's structure package is attached to the
lane's stable package.
-/
theorem tStructure_stablePackage_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.tStructure.stablePackage = P.stablePackage :=
  Eq.trans P.structures.tStructure_stablePackage_eq
    P.structures_stablePackage_eq

/--
The compact-geometric closed object seen by the lane's `t`-structure agrees
with the analytic Tate stabilization used by the lane's comparison package.
-/
theorem tStructure_closedObject_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.structures.tStructure.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.comparison.tateComparison.analyticStabilization :=
  Eq.trans
    (AnalyticMotiveStructures.tStructure_closedObject_compatibility
      P.structures)
    (structures_closedObject_compatibility P)

/-- The downstream trace realization package. -/
def trace (P : AnalyticMotivesLanePackage) :
    AnalyticTraceRealization :=
  P.traceRealization

/--
The lane's trace boundary presentation and reconstruction comparison are
attached to the same contour-admissible bulk.
-/
theorem trace_boundary_bulk_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.boundaryPresentation.boundaryStream.bulk =
      P.traceRealization.reconstruction.bulkToBoundary.bulk :=
  AnalyticTraceRealization.boundary_bulk_compatibility
    P.traceRealization

/--
The lane's Hilbert/GNS boundary presentation and boundary stream presentation
are attached to the same contour-admissible bulk.
-/
theorem trace_hilbert_boundary_bulk_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.boundaryPresentation.hilbertSource.boundaryPresentation.bulk =
      P.traceRealization.boundaryPresentation.boundaryStream.bulk :=
  AnalyticTraceRealization.hilbert_boundary_bulk_compatibility
    P.traceRealization

/--
The lane's Hilbert/GNS boundary presentation and boundary stream presentation
use the same packet.
-/
theorem trace_hilbert_boundary_packet_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.boundaryPresentation.hilbertSource.boundaryPresentation.packet =
      P.traceRealization.boundaryPresentation.boundaryStream.packet :=
  AnalyticTraceRealization.hilbert_boundary_packet_compatibility
    P.traceRealization

/--
The lane's packet-comparison trace realization uses the same vertical channel
as the lane's trace-channel aggregate.
-/
theorem trace_channel_packet_vertical_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.packet.vertical =
      P.traceRealization.channelRealization.vertical :=
  AnalyticTraceRealization.channel_packet_vertical_compatibility
    P.traceRealization

/--
The lane's archimedean/Binet trace realization uses the same packet
realization as the lane's trace-channel aggregate.
-/
theorem trace_channel_archimedean_packet_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.archimedean.packetRealization =
      P.traceRealization.channelRealization.packet :=
  AnalyticTraceRealization.channel_archimedean_packet_compatibility
    P.traceRealization

/--
The lane's archimedean/Binet channel agrees with the lane's aggregate vertical
archimedean channel.
-/
theorem trace_channel_archimedeanChannel_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.archimedean.archimedeanChannel =
      P.traceRealization.channelRealization.vertical.archimedeanChannel :=
  AnalyticTraceRealization.channel_archimedeanChannel_compatibility
    P.traceRealization

/--
The lane's trace vertical channel sum agrees with the owner trace-calculus
vertical channel sum.
-/
theorem trace_channelSum_eq
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.vertical.channelSum =
      verticalTraceChannelSum
        P.traceRealization.channelRealization.vertical.packet
        P.traceRealization.channelRealization.vertical.contourFamily
        P.traceRealization.channelRealization.vertical.height :=
  AnalyticTraceRealization.channelSum_eq P.traceRealization

/--
The lane's trace vertical archimedean channel agrees with the owner
trace-calculus archimedean channel.
-/
theorem trace_archimedean_channel_eq
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.vertical.archimedeanChannel =
      archimedeanVerticalTraceChannel
        P.traceRealization.channelRealization.vertical.packet
        P.traceRealization.channelRealization.vertical.contourFamily
        P.traceRealization.channelRealization.vertical.height :=
  AnalyticTraceRealization.archimedean_channel_eq P.traceRealization

/--
The lane's packet boundary-defect Gram agrees with its packet norm square.
-/
theorem trace_packet_gram_eq_normSq
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.packet.boundaryDefectGram =
      P.traceRealization.channelRealization.packet.packetNormSq :=
  AnalyticTraceRealization.packet_gram_eq_normSq P.traceRealization

/--
The lane's trace packet norm square agrees with the owner trace-calculus
packet norm for the lane's aggregate vertical channel.
-/
theorem trace_packet_normSq_eq_owner
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.packet.packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        P.traceRealization.channelRealization.vertical.packet 0 :=
  AnalyticTraceRealization.packet_normSq_eq_owner P.traceRealization

/--
The lane's packet boundary-defect Gram agrees with the owner trace-calculus
packet norm for the lane's aggregate vertical channel.
-/
theorem trace_packet_gram_eq_owner
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.channelRealization.packet.boundaryDefectGram =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq
        P.traceRealization.channelRealization.vertical.packet 0 :=
  AnalyticTraceRealization.packet_gram_eq_owner P.traceRealization

/--
The lane's trace boundary presentation and channel realization use the same
packet.
-/
theorem trace_packet_compatibility
    (P : AnalyticMotivesLanePackage) :
    P.traceRealization.boundaryPresentation.boundaryStream.packet =
      P.traceRealization.channelRealization.vertical.packet :=
  AnalyticTraceRealization.packet_compatibility P.traceRealization

end AnalyticMotivesLanePackage

/--
Downstream trace-weight compatibility for the top-level analytic motives lane.
The lane package itself remains the bulk/stable/structure/trace/comparison
assembly; this package records trace positivity evidence for its weight data.
-/
structure AnalyticMotivesLaneTraceWeightCompatibility
    (P : AnalyticMotivesLanePackage) where
  structuresTrace :
    AnalyticMotiveStructuresTraceCompatibility P.structures

namespace AnalyticMotivesLaneTraceWeightCompatibility

/-- Trace compatibility data for the lane's structure package. -/
def structuresTraceData {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P) :
    AnalyticMotiveStructuresTraceCompatibility P.structures :=
  C.structuresTrace

/-- Boundary-stream compatibility at a lane weight index. -/
def boundaryAt {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryStreamWeightCompatibility
      P.structures.weight.geometric.weightCandidate i :=
  C.structuresTrace.boundaryAt i

/-- Packet/Hilbert compatibility at a lane weight index. -/
def packetHilbertAt {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    PacketHilbertWeightCompatibility (C.boundaryAt i) :=
  C.structuresTrace.packetHilbertAt i

/-- The boundary presentation at an index is attached to the selected weight stratum bulk. -/
theorem boundary_bulk_eq {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    (C.boundaryAt i).boundaryPresentation.bulk =
      P.structures.weight.bulkAt i :=
  AnalyticMotiveStructuresTraceCompatibility.boundary_bulk_eq
    C.structuresTrace i

/-- The boundary stream at an index lies in the positive cone. -/
theorem boundary_stream_mem_positiveCone
    {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.InPositiveCone
      (C.boundaryAt i).stream :=
  AnalyticMotiveStructuresTraceCompatibility.boundary_stream_mem_positiveCone
    C.structuresTrace i

/-- The packet norm square at an index is nonnegative. -/
theorem packet_normSq_nonnegative
    {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).normSq :=
  AnalyticMotiveStructuresTraceCompatibility.packet_normSq_nonnegative
    C.structuresTrace i

/-- The Hilbert/GNS scalar at an index is nonnegative. -/
theorem hilbert_scalar_nonnegative
    {P : AnalyticMotivesLanePackage}
    (C : AnalyticMotivesLaneTraceWeightCompatibility P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).hilbertPresentation.gnsScalar :=
  AnalyticMotiveStructuresTraceCompatibility.hilbert_scalar_nonnegative
    C.structuresTrace i

end AnalyticMotivesLaneTraceWeightCompatibility

/--
Top-level analytic motives lane package whose stable category is generated
from the bulk contour-correspondence construction.
-/
structure BulkGeneratedAnalyticMotivesLanePackage where
  generatedStable : BulkGeneratedStableAnalyticMotivePackage
  structures : AnalyticMotiveStructures
  traceRealization : AnalyticTraceRealization
  comparison : DMgmQQComparisonPackage
  structures_stablePackage_eq :
    structures.stablePackage = generatedStable.forget
  comparison_stablePackage_eq :
    comparison.stableCoherence.stablePackage = generatedStable.forget

namespace BulkGeneratedAnalyticMotivesLanePackage

/-- The bulk-generated stable analytic motive package. -/
def stable (P : BulkGeneratedAnalyticMotivesLanePackage) :
    BulkGeneratedStableAnalyticMotivePackage :=
  P.generatedStable

/-- The bulk construction generating the stable category. -/
def bulk (P : BulkGeneratedAnalyticMotivesLanePackage) :
    BulkAnalyticMotiveConstruction :=
  P.generatedStable.bulkConstruction

/-- The non-functorial stable package seen by structures and comparison data. -/
def stablePackage (P : BulkGeneratedAnalyticMotivesLanePackage) :
    StableAnalyticMotivePackage :=
  P.generatedStable.forget

/-- The structure package is attached to the bulk-generated stable package. -/
theorem structures_stablePackage_compatibility
    (P : BulkGeneratedAnalyticMotivesLanePackage) :
    P.structures.stablePackage = P.stablePackage :=
  P.structures_stablePackage_eq

/-- The comparison package is attached to the bulk-generated stable package. -/
theorem comparison_stablePackage_compatibility
    (P : BulkGeneratedAnalyticMotivesLanePackage) :
    P.comparison.stableCoherence.stablePackage =
      P.stablePackage :=
  P.comparison_stablePackage_eq

/-- The rational category in the lane is the one from the bulk construction. -/
def rationalCategory (P : BulkGeneratedAnalyticMotivesLanePackage) :
    RationalContourCategoryData :=
  P.bulk.rationalCategory

/--
The lane's rational transfers are linearized from the bulk contour
correspondence calculus.
-/
theorem rational_correspondenceLaws_compatibility
    (P : BulkGeneratedAnalyticMotivesLanePackage) :
    P.rationalCategory.correspondenceLaws =
      P.bulk.correspondenceCalculus.laws :=
  BulkAnalyticMotiveConstruction.rational_correspondenceLaws_compatibility
    P.bulk

/--
The compact-geometric closed object seen by the structures agrees with the
bulk-generated stable package.
-/
theorem structures_closedObject_compatibility
    (P : BulkGeneratedAnalyticMotivesLanePackage) :
    P.structures.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject :=
  congrArg
    (fun S =>
      S.compactLayer.compactGeometric.thickClosure.closedObject)
    P.structures_stablePackage_eq

/--
The compact-geometric closed object seen by the comparison package agrees with
the bulk-generated stable package.
-/
theorem comparison_closedObject_compatibility
    (P : BulkGeneratedAnalyticMotivesLanePackage) :
    P.comparison.stableCoherence.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject :=
  congrArg
    (fun S =>
      S.compactLayer.compactGeometric.thickClosure.closedObject)
    P.comparison_stablePackage_eq

end BulkGeneratedAnalyticMotivesLanePackage

/--
Top-level analytic motives lane package using the enriched bulk-generated
comparison surface.
-/
structure BulkGeneratedAnalyticMotivesComparisonLane where
  comparison : DMgmQQBulkGeneratedComparisonPackage
  structures : AnalyticMotiveStructures
  traceRealization : AnalyticTraceRealization
  structures_stablePackage_eq :
    structures.stablePackage = comparison.generatedStable.forget

namespace BulkGeneratedAnalyticMotivesComparisonLane

/-- The enriched bulk-generated comparison package. -/
def comparisonData (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    DMgmQQBulkGeneratedComparisonPackage :=
  P.comparison

/-- The bulk-generated stable analytic motive package. -/
def stable (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    BulkGeneratedStableAnalyticMotivePackage :=
  P.comparison.generatedStable

/-- The bulk construction generating the analytic stable category. -/
def bulk (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    BulkAnalyticMotiveConstruction :=
  P.comparison.bulk

/-- The non-functorial stable package seen by structures and comparison data. -/
def stablePackage (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    StableAnalyticMotivePackage :=
  P.comparison.generatedStable.forget

/-- The structures are attached to the bulk-generated stable package. -/
theorem structures_stablePackage_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.structures.stablePackage = P.stablePackage :=
  P.structures_stablePackage_eq

/-- The comparison is attached to the bulk-generated stable package. -/
theorem comparison_stablePackage_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.comparison.comparison.stableCoherence.stablePackage =
      P.stablePackage :=
  DMgmQQBulkGeneratedComparisonPackage.stablePackage_compatibility
    P.comparison

/-- The rational category in the lane is generated by the bulk construction. -/
def rationalCategory (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    RationalContourCategoryData :=
  P.bulk.rationalCategory

/--
The lane's rational transfers are linearized from the bulk contour
correspondence calculus.
-/
theorem rational_correspondenceLaws_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.rationalCategory.correspondenceLaws =
      P.bulk.correspondenceCalculus.laws :=
  BulkAnalyticMotiveConstruction.rational_correspondenceLaws_compatibility
    P.bulk

/-- The correspondence comparison is attached to the bulk contour calculus. -/
theorem correspondence_analyticCalculus_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.comparison.correspondenceComparison.analyticCalculus =
      P.bulk.correspondenceCalculus :=
  DMgmQQBulkGeneratedComparisonPackage.correspondence_analyticCalculus_compatibility
    P.comparison

/-- The analytic Tate object in the comparison is generated by the bulk construction. -/
theorem analyticTate_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.comparison.tateComparison.tateComparison.analyticTate =
      P.bulk.presheaves.tate.tateObject :=
  DMgmQQBulkGeneratedComparisonPackage.analyticTate_compatibility
    P.comparison

/-- The analytic Tate stabilization in the comparison is generated by the bulk construction. -/
theorem analyticStabilization_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.comparison.tateComparison.tateComparison.analyticStabilization =
      P.bulk.presheaves.tate.forget :=
  DMgmQQBulkGeneratedComparisonPackage.analyticStabilization_compatibility
    P.comparison

/--
The structures see the same compact-geometric closed object as the
bulk-generated stable package.
-/
theorem structures_closedObject_compatibility
    (P : BulkGeneratedAnalyticMotivesComparisonLane) :
    P.structures.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      P.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject :=
  congrArg
    (fun S =>
      S.compactLayer.compactGeometric.thickClosure.closedObject)
    P.structures_stablePackage_eq

end BulkGeneratedAnalyticMotivesComparisonLane

/--
Trace-weight compatibility for the enriched bulk-generated analytic motives
comparison lane.
-/
structure BulkGeneratedAnalyticMotivesComparisonTraceWeight
    (P : BulkGeneratedAnalyticMotivesComparisonLane) where
  structuresTrace :
    AnalyticMotiveStructuresTraceCompatibility P.structures

namespace BulkGeneratedAnalyticMotivesComparisonTraceWeight

/-- Trace compatibility data for the enriched lane's structure package. -/
def structuresTraceData
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P) :
    AnalyticMotiveStructuresTraceCompatibility P.structures :=
  C.structuresTrace

/-- Boundary-stream compatibility at an enriched lane weight index. -/
def boundaryAt
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryStreamWeightCompatibility
      P.structures.weight.geometric.weightCandidate i :=
  C.structuresTrace.boundaryAt i

/-- Packet/Hilbert compatibility at an enriched lane weight index. -/
def packetHilbertAt
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    PacketHilbertWeightCompatibility (C.boundaryAt i) :=
  C.structuresTrace.packetHilbertAt i

/-- The boundary presentation at an index is attached to the selected weight stratum bulk. -/
theorem boundary_bulk_eq
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    (C.boundaryAt i).boundaryPresentation.bulk =
      P.structures.weight.bulkAt i :=
  AnalyticMotiveStructuresTraceCompatibility.boundary_bulk_eq
    C.structuresTrace i

/-- The boundary stream at an index lies in the positive cone. -/
theorem boundary_stream_mem_positiveCone
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    BoundaryTraceStream.InPositiveCone
      (C.boundaryAt i).stream :=
  AnalyticMotiveStructuresTraceCompatibility.boundary_stream_mem_positiveCone
    C.structuresTrace i

/-- The packet norm square at an index is nonnegative. -/
theorem packet_normSq_nonnegative
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).normSq :=
  AnalyticMotiveStructuresTraceCompatibility.packet_normSq_nonnegative
    C.structuresTrace i

/-- The Hilbert/GNS scalar at an index is nonnegative. -/
theorem hilbert_scalar_nonnegative
    {P : BulkGeneratedAnalyticMotivesComparisonLane}
    (C : BulkGeneratedAnalyticMotivesComparisonTraceWeight P)
    (i : P.structures.weight.geometric.weightCandidate.StratumIndex) :
    0 ≤ (C.packetHilbertAt i).hilbertPresentation.gnsScalar :=
  AnalyticMotiveStructuresTraceCompatibility.hilbert_scalar_nonnegative
    C.structuresTrace i

end BulkGeneratedAnalyticMotivesComparisonTraceWeight

end AnalyticMotives
end LFunctions
end Boundary
