import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.Owner

/-!
# Packet comparison surface

This file exposes the existing packet reconstruction identities as the
packet-level comparison API for analytic-motive trace calculus.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace AnalyticMotives

/-- The completed boundary-defect Gram is the completed packet norm square. -/
theorem boundaryDefectGram_eq_packetNormSq
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram f =
      ZetaAdmissibleFunction.zetaCompletedPacketNormSq f 0 :=
  ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The completed packet norm square is nonnegative. -/
theorem packetNormSq_nonnegative_of_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    0 ≤ ZetaAdmissibleFunction.zetaCompletedPacketNormSq f 0 :=
  ZetaAdmissibleFunction.zetaCompletedPacketNormSq_nonnegative_of_boundaryDefect f

/-- The boundary-defect Gram decomposes into prime, archimedean, and correction components. -/
theorem boundaryDefectGram_eq_realShadowComponents
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram f =
      ZetaPacketEnsemble.primePacketGram
          (ZetaAdmissibleFunction.zetaCompletedBoundaryDefect f) +
        ZetaPacketEnsemble.archimedeanPacketGram
          (ZetaAdmissibleFunction.zetaCompletedBoundaryDefect f) +
        ZetaPacketEnsemble.correctionPacketGram
          (ZetaAdmissibleFunction.zetaCompletedBoundaryDefect f) :=
  ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram_eq_realShadowComponents f

end AnalyticMotives

end
end LFunctions
end Boundary
