import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner

/-!
# Analytic-motive Hilbert/GNS realization

This file exposes the already-owned completed boundary Hilbert source and GNS
kernel as the Hilbert realization surface of the analytic trace calculus.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace AnalyticMotives

/-- Analytic-motive-facing name for completed boundary Hilbert sources. -/
abbrev BoundaryHilbertSource :=
  ZetaAdmissibleFunction.CompletedBoundaryHilbertSource

/-- The canonical Hilbert source attached to an admissible zeta test packet. -/
def boundaryHilbertSource
    (f : ZetaAdmissibleFunction) : BoundaryHilbertSource :=
  ZetaAdmissibleFunction.completedBoundaryHilbertSource f

/-- The completed boundary GNS kernel. -/
def boundaryGNSKernel
    (X Y : BoundaryHilbertSource) : ℝ :=
  ZetaAdmissibleFunction.completedBoundaryGNSKernel X Y

/-- The completed boundary GNS kernel is nonnegative on the diagonal. -/
theorem boundaryGNSKernel_self_nonnegative
    (X : BoundaryHilbertSource) :
    0 ≤ boundaryGNSKernel X X :=
  ZetaAdmissibleFunction.completedBoundaryGNSKernel_self_nonnegative X

/-- The real-shadow GNS norm square of the canonical source. -/
def boundaryRealShadowGNSNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaAdmissibleFunction.completedBoundaryRealShadowGNSNormSq f

/-- The real-shadow GNS norm square is nonnegative. -/
theorem boundaryRealShadowGNSNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ boundaryRealShadowGNSNormSq f :=
  ZetaAdmissibleFunction.completedBoundaryRealShadowGNSNormSq_nonnegative f

/-- The Hermitian/GNS scalar attached to a completed boundary Hilbert source. -/
def boundaryHermitianGNSScalar
    (X : BoundaryHilbertSource) : ℝ :=
  ZetaAdmissibleFunction.completedBoundaryHermitianGNSScalar X

/-- The Hermitian/GNS scalar is nonnegative. -/
theorem boundaryHermitianGNSScalar_nonnegative
    (X : BoundaryHilbertSource) :
    0 ≤ boundaryHermitianGNSScalar X :=
  ZetaAdmissibleFunction.completedBoundaryHermitianGNSScalar_nonnegative X

end AnalyticMotives

end
end LFunctions
end Boundary
