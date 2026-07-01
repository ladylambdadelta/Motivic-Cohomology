import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.Owner

/-!
# Analytic-motive boundary streams

This file exposes the completed boundary weight stream from the RH lane under
an analytic-motive-facing name.  It does not define a new category or a new
localization; it packages the already-owned trace calculus API.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace AnalyticMotives

/-- Analytic-motive-facing name for the completed boundary trace stream. -/
abbrev BoundaryTraceStream :=
  ZetaAdmissibleFunction.CompletedBoundaryWeightStream

/-- The boundary trace stream realized by an admissible zeta test packet. -/
def boundaryTraceStream
    (f : ZetaAdmissibleFunction) : BoundaryTraceStream :=
  ZetaAdmissibleFunction.completedBoundaryWeightStream f

/-- Boundary trace streams have square representatives when the underlying owner stream does. -/
def BoundaryTraceStream.HasSquareRepresentatives
    (X : BoundaryTraceStream) : Prop :=
  ZetaAdmissibleFunction.CompletedBoundaryWeightStream.SquareRepresentativesNonnegative X

/-- Boundary trace streams have lower-weight absorption when the underlying owner stream does. -/
def BoundaryTraceStream.HasLowerWeightAbsorption
    (X : BoundaryTraceStream) : Prop :=
  ZetaAdmissibleFunction.CompletedBoundaryWeightStream.HasLowerWeightAbsorption X

/-- The positive cone is inherited from the completed boundary weight stream owner. -/
def BoundaryTraceStream.InPositiveCone
    (X : BoundaryTraceStream) : Prop :=
  ZetaAdmissibleFunction.CompletedBoundaryWeightStream.InPositiveCone X

/-- The realized stream lies in the completed positive cone. -/
theorem boundaryTraceStream_mem_positiveCone
    (f : ZetaAdmissibleFunction) :
    BoundaryTraceStream.InPositiveCone (boundaryTraceStream f) :=
  ZetaAdmissibleFunction.completedBoundaryWeightStream_mem_positiveCone f

/-- The realized stream satisfies pointwise weight-triangular transport. -/
theorem boundaryTraceStream_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        ((boundaryTraceStream f).object N) +
      ((boundaryTraceStream f).object N).debtAbsorption =
    FiniteBoundaryWeightObject.finitePartRepresentative
        ((boundaryTraceStream f).object N) :=
  ZetaAdmissibleFunction.completedBoundaryWeightStream_weightTriangularTransport N f

/-- The trace scalar is the real completed boundary channel. -/
theorem boundaryTraceStream_scalar_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    (boundaryTraceStream f).scalar =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  ZetaAdmissibleFunction.completedBoundaryWeightStream_scalar_eq_boundaryChannel_re f

end AnalyticMotives

end
end LFunctions
end Boundary
