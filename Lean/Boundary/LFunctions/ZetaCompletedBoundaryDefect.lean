import Boundary.LFunctions.ZetaPacketReconstruction
import Boundary.LFunctions.WeilCriterion

/-!
# Boundary completed zeta defect

This file owns the completed boundary-defect operator attached to an
admissible probe. It packages the prime, archimedean, and completion/correction
components into the single boundary object whose Gram norm is the packet
energy.

The comparison to the completed Weil form is deferred to the comparison file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed zeta boundary defect attached to an admissible probe. -/
noncomputable def zetaCompletedBoundaryDefect (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaPacketAsEnsemble f

/-- The prime component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectPrime (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaPrimePacketAsEnsemble f

/-- The archimedean component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectArchimedean (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaArchimedeanPacketAsEnsemble f

/-- The completion/correction component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectCorrection (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaCorrectionPacketAsEnsemble f

/-- The completed zeta boundary defect decomposes into prime, archimedean, and correction parts. -/
theorem zetaCompletedBoundaryDefect_decomposition (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefect f =
      zetaCompletedBoundaryDefectPrime f +
        zetaCompletedBoundaryDefectArchimedean f +
        zetaCompletedBoundaryDefectCorrection f := by
  rfl

/-- The completed zeta boundary defect Gram norm square. -/
noncomputable def zetaCompletedBoundaryDefectGram (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPacketEnsemble.normSq (zetaCompletedBoundaryDefect f)

/-- The completed boundary defect Gram norm square is the packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_packetNormSq (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f := by
  rfl

/-- The completed boundary defect Gram norm is nonnegative. -/
theorem zetaCompletedBoundaryDefectGram_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectGram f := by
  unfold zetaCompletedBoundaryDefectGram zetaCompletedBoundaryDefect
  exact ZetaPacketEnsemble.normSq_nonneg (zetaPacketAsEnsemble f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
