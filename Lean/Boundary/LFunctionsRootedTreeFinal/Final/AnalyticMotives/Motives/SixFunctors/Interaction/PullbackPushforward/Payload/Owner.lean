import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.Owner

/-!
# Payload of the compact pullback-pushforward square

This file names the endpoint payloads carried by the concrete square in which
vertical maps are compact-generator pullbacks along a probe and horizontal maps
are compact-generator pushforwards along a morphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest corner imported rectangles in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
    morphism ++
  TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
    probe

/-- Northeast corner imported rectangles in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
    morphism ++
  TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
    probe

/-- Southwest corner imported rectangles in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
    morphism ++
  TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
    probe

/-- Southeast corner imported rectangles in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southeastImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
    morphism ++
  TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
    probe

/-- Northwest corner imported-rectangle count in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount
    probe

/-- Northeast corner imported-rectangle count in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount
    probe

/-- Southwest corner imported-rectangle count in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount
    probe

/-- Southeast corner imported-rectangle count in the compact pullback-pushforward square. -/
def TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    Nat :=
  TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount
    morphism +
  TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount
    probe

/-- Northwest corner count is the length of its imported-rectangle list. -/
theorem TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe).length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_length
        morphism)
      (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_length
        probe))
    (Eq.sym
      (List.length_append
        (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
          morphism)
        (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
          probe)))

/-- Northeast corner count is the length of its imported-rectangle list. -/
theorem TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        probe =
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        probe).length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_length
        morphism)
      (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_length
        probe))
    (Eq.sym
      (List.length_append
        (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
          morphism)
        (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles
          probe)))

/-- Southwest corner count is the length of its imported-rectangle list. -/
theorem TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        probe =
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        probe).length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_length
        morphism)
      (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_length
        probe))
    (Eq.sym
      (List.length_append
        (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles
          morphism)
        (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
          probe)))

/-- Southeast corner count is the length of its imported-rectangle list. -/
theorem TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        probe =
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        probe).length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_length
        morphism)
      (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_length
        probe))
    (Eq.sym
      (List.length_append
        (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles
          morphism)
        (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles
          probe)))

end AnalyticMotives
end LFunctions
end Boundary
