import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.TraceBesselCore

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

theorem boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_core_owner
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_traceBessel_core hBoundary)

theorem boundaryRiemannHypothesis_of_zeroSideBoundaryIdentification_traceBessel_core_owner
    (zeroBoundary :
      ZetaCompletedAutocorrelationZeroSideBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_core_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification_core
      zeroBoundary)

theorem boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_traceBessel_core_owner
    (commonLimit :
      ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_core_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
      commonLimit)

end
end LFunctions
end Boundary
