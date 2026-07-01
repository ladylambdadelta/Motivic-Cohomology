import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.HilbertRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCalculus.PacketComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.HilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.TraceWeightCompatibility.BoundaryStream.Owner

/-!
# Packet and Hilbert positivity compatibility

This file owns compatibility between geometric weights and the packet/Hilbert
positivity surfaces exposed by trace realization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Packet and Hilbert/GNS positivity compatibility for a geometric weight stratum.
This is downstream evidence attached to a boundary-stream compatibility object;
it does not define the geometric weight data.
-/
structure PacketHilbertWeightCompatibility
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    (B : BoundaryStreamWeightCompatibility W i) where
  hilbertPresentation : HilbertSourcePresentation
  boundaryPresentation_eq :
    hilbertPresentation.boundaryPresentation =
      B.boundaryPresentation
  packetNormSq : ℝ
  packetNormSq_eq :
    packetNormSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq B.packet 0
  packetNormSq_nonnegative :
    0 ≤ packetNormSq
  gnsScalar_nonnegative :
    0 ≤ hilbertPresentation.gnsScalar

namespace PacketHilbertWeightCompatibility

/-- The Hilbert/GNS presentation used by packet positivity compatibility. -/
def presentation {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    HilbertSourcePresentation :=
  C.hilbertPresentation

/-- The packet norm square in packet positivity compatibility data. -/
def normSq {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) : ℝ :=
  C.packetNormSq

/-- The Hilbert presentation uses the same boundary presentation. -/
theorem boundaryPresentation_compatibility
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    C.hilbertPresentation.boundaryPresentation =
      B.boundaryPresentation :=
  C.boundaryPresentation_eq

/-- The packet norm square agrees with the owner packet norm. -/
theorem normSq_eq_owner
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    C.normSq =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq B.packet 0 :=
  C.packetNormSq_eq

/-- The compatible packet norm square is nonnegative. -/
theorem normSq_nonnegative
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    0 ≤ C.normSq :=
  C.packetNormSq_nonnegative

/-- The compatible Hilbert/GNS scalar is nonnegative. -/
theorem hilbertScalar_nonnegative
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    0 ≤ C.hilbertPresentation.gnsScalar :=
  C.gnsScalar_nonnegative

/-- The compatible Hilbert source agrees with the owner Hilbert source. -/
theorem hilbertSource_eq_owner
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    C.hilbertPresentation.hilbertSource =
      boundaryHilbertSource C.hilbertPresentation.boundaryPresentation.packet :=
  C.hilbertPresentation.hilbertSource_eq

/-- The compatible Hilbert scalar agrees with the owner GNS scalar. -/
theorem hilbertScalar_eq_owner
    {S : AnalyticMotivicStableInfinityInterface}
    {W : GeometricWeightCandidate S}
    {i : W.StratumIndex}
    {B : BoundaryStreamWeightCompatibility W i}
    (C : PacketHilbertWeightCompatibility B) :
    C.hilbertPresentation.gnsScalar =
      boundaryHermitianGNSScalar C.hilbertPresentation.hilbertSource :=
  C.hilbertPresentation.gnsScalar_eq

end PacketHilbertWeightCompatibility

end AnalyticMotives
end LFunctions
end Boundary
