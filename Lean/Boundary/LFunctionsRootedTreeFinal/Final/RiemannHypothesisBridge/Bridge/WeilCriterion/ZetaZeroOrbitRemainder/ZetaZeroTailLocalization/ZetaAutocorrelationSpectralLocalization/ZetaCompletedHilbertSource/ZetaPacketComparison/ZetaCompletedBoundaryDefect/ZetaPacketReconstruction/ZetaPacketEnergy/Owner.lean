import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketEnergy.ZetaPacketGram.Owner

/-!
# Boundary zeta packet energy

This file packages the packet-side norm-square data under owner-level energy
names. It does not attempt to connect the packet algebra to the completed Weil
form yet; it only exposes the finite packet energy surface in canonical form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaPacketEnsemble

/-- The total packet energy of a finite packet ensemble. -/
def packetEnergy (x : ZetaPacketEnsemble) : ℝ :=
  normSq x

/-- The prime contribution to the packet energy. -/
def packetEnergyPrime (x : ZetaPacketEnsemble) : ℝ :=
  primePacketGram x

/-- The archimedean contribution to the packet energy. -/
def packetEnergyArchimedean (x : ZetaPacketEnsemble) : ℝ :=
  archimedeanPacketGram x

/-- The correction contribution to the packet energy. -/
def packetEnergyCorrection (x : ZetaPacketEnsemble) : ℝ :=
  correctionPacketGram x

/-- The packet energy is definitionally the packet norm square. -/
theorem packetEnergy_eq_normSq (x : ZetaPacketEnsemble) :
    packetEnergy x = normSq x := by
  exact Eq.refl _

/-- The prime packet energy is definitionally the prime Gram contribution. -/
theorem packetEnergyPrime_eq (x : ZetaPacketEnsemble) :
    packetEnergyPrime x = primePacketGram x := by
  exact Eq.refl _

/-- The archimedean packet energy is definitionally the archimedean Gram contribution. -/
theorem packetEnergyArchimedean_eq (x : ZetaPacketEnsemble) :
    packetEnergyArchimedean x = archimedeanPacketGram x := by
  exact Eq.refl _

/-- The correction packet energy is definitionally the correction Gram contribution. -/
theorem packetEnergyCorrection_eq (x : ZetaPacketEnsemble) :
    packetEnergyCorrection x = correctionPacketGram x := by
  exact Eq.refl _

/-- The packet energy decomposes into the three family contributions. -/
theorem packetEnergy_eq_sum (x : ZetaPacketEnsemble) :
    packetEnergy x =
      packetEnergyPrime x + packetEnergyArchimedean x + packetEnergyCorrection x := by
  change normSq x = primePacketGram x + archimedeanPacketGram x + correctionPacketGram x
  exact zetaPacketNormSquare x

/-- The packet energy is nonnegative. -/
theorem packetEnergy_nonneg (x : ZetaPacketEnsemble) :
    0 ≤ packetEnergy x := by
  change 0 ≤ normSq x
  exact normSq_nonneg x

end ZetaPacketEnsemble

end
end LFunctions
end Boundary
