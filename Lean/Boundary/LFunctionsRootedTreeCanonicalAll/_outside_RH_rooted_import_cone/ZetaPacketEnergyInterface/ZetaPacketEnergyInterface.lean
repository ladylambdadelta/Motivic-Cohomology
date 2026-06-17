import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketEnergy.ZetaPacketEnergy

/-!
# Boundary packet energy interface

This file names the packet-energy surface in the owner namespace so later
comparison lemmas can import a single stable module.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The owner-level packet energy on a finite packet ensemble. -/
abbrev zetaPacketEnergy := ZetaPacketEnsemble.packetEnergy

/-- The owner-level prime packet energy. -/
abbrev zetaPacketEnergyPrime := ZetaPacketEnsemble.packetEnergyPrime

/-- The owner-level archimedean packet energy. -/
abbrev zetaPacketEnergyArchimedean := ZetaPacketEnsemble.packetEnergyArchimedean

/-- The owner-level correction packet energy. -/
abbrev zetaPacketEnergyCorrection := ZetaPacketEnsemble.packetEnergyCorrection

/-- The packet energy is definitionally the packet norm square. -/
theorem zetaPacketEnergy_eq_normSq (x : ZetaPacketEnsemble) :
    zetaPacketEnergy x = ZetaPacketEnsemble.normSq x := by
  rfl

/-- The packet energy decomposes into the three packet-family contributions. -/
theorem zetaPacketEnergy_eq_sum (x : ZetaPacketEnsemble) :
    zetaPacketEnergy x =
      zetaPacketEnergyPrime x +
      zetaPacketEnergyArchimedean x +
      zetaPacketEnergyCorrection x := by
  exact ZetaPacketEnsemble.packetEnergy_eq_sum x

/-- The packet energy is nonnegative. -/
theorem zetaPacketEnergy_nonneg (x : ZetaPacketEnsemble) :
    0 ≤ zetaPacketEnergy x := by
  exact ZetaPacketEnsemble.packetEnergy_nonneg x

end
end LFunctions
end Boundary
