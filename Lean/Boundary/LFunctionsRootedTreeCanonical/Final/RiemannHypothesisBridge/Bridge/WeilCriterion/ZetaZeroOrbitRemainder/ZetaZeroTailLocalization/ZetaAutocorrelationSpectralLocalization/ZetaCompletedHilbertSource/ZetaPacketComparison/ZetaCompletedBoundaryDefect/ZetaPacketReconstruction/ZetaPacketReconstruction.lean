import Boundary.LFunctions.ZetaAdmissibleTransform
import Boundary.LFunctions.ZetaPacketDecomposition
import Boundary.LFunctions.ZetaPacketEnergy
import Boundary.LFunctions.ZetaLogBoundaryDefect
import Boundary.LFunctions.ZetaCompletionCorrection

/-!
# Boundary zeta packet reconstruction

This file owns the admissible-probe-to-packet reconstruction map. The packet is
assembled from the logarithmic prime-power defect data, the archimedean defect,
and the completion correction.

The packet object is finite because the admissible carrier has compact support
on the logarithmic line; the prime-power window is cut off by a bound extracted
from that compact support.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaPacketEnsemble

/-- The packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (a : ℝ) : ZetaPacketEnsemble :=
  Finsupp.single ℓ a

end ZetaPacketEnsemble

namespace ZetaAdmissibleFunction

/-- Compact support provides an explicit upper bound for the logarithmic support. -/
theorem exists_zetaPacketSupportRadius (f : ZetaAdmissibleFunction) :
    ∃ B : ℝ, ∀ x ∈ tsupport f.toZetaTestFunction, x ≤ B := by
  obtain ⟨B, hB⟩ := IsCompact.bddAbove (f.toZetaTestFunction.hasCompactSupport.isCompact)
  exact ⟨B, hB⟩

/-- The prime packet weight on a prime-power label. -/
def zetaPrimePacketWeight : ZetaPacketLabel → ℝ
  | .prime p m =>
      if _hp : Nat.Prime p then
        Real.log p / Real.sqrt (p ^ m)
      else
        0
  | _ => 0

theorem zetaPrimePacketWeight_prime (p m : ℕ) (hp : Nat.Prime p) :
    zetaPrimePacketWeight (.prime p m) = Real.log p / Real.sqrt (p ^ m) := by
  unfold zetaPrimePacketWeight
  exact if_pos hp

theorem zetaPrimePacketWeight_nonprime (ℓ : ZetaPacketLabel) (h : ¬ ∃ p m, ℓ = .prime p m) :
    zetaPrimePacketWeight ℓ = 0 := by
  cases ℓ with
  | prime p m =>
      exfalso
      apply h
      exact ⟨p, m, rfl⟩
  | archimedean =>
      rfl
  | correction =>
      rfl

/-- The finite set of prime-power indices used by the prime-side reconstruction. -/
def zetaPacketPrimeSupport (B : ℝ) : Finset (ℕ × ℕ) :=
  Finset.product
    (Finset.range (Nat.ceil (Real.exp B) + 1))
    (Finset.range (Nat.ceil (Real.exp B) + 1))

/-- The prime packet associated to an admissible function. -/
def zetaPrimePacketAsEnsemble (f : ZetaAdmissibleFunction) (B : ℝ) :
    ZetaPacketEnsemble :=
  ∑ ℓ in zetaPacketPrimeSupport B,
    ZetaPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (Complex.re
        (zetaPrimePacketWeight (ZetaPacketLabel.prime ℓ.1 ℓ.2) •
          ZetaTestFunction.primePacketTranslationDefect ℓ.1 ℓ.2 f.toZetaTestFunction' 0))

/-- The archimedean packet associated to an admissible function. -/
def zetaArchimedeanPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .archimedean
    (Complex.re (ZetaTestFunction.archimedeanTranslationDefect 0 f.toZetaTestFunction' 0))

/-- The completion/correction packet associated to an admissible function. -/
noncomputable def zetaCorrectionPacketAsEnsemble (_f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .correction zetaCompletionCorrectionPacketCoordinate

/-- The canonical completed zeta packet attached to an admissible probe. -/
def zetaPacketAsEnsemble (f : ZetaAdmissibleFunction) (B : ℝ) :
    ZetaPacketEnsemble :=
  zetaPrimePacketAsEnsemble f B +
    zetaArchimedeanPacketAsEnsemble f +
    zetaCorrectionPacketAsEnsemble f

/-- The packet is finite-support because it is a finite sum of singletons. -/
theorem zetaPacketAsEnsemble_finiteSupport (f : ZetaAdmissibleFunction) :
    ∀ B : ℝ, Finite ((zetaPacketAsEnsemble f B).support : Set ZetaPacketLabel) := by
  intro B
  exact Set.toFinite ((zetaPacketAsEnsemble f B).support : Set ZetaPacketLabel)

/-- The packet norm-square of the reconstructed packet. -/
def zetaCompletedPacketNormSq (f : ZetaAdmissibleFunction) (B : ℝ) : ℝ :=
  ZetaPacketEnsemble.normSq (zetaPacketAsEnsemble f B)

/-- The reconstructed packet norm-square is nonnegative. -/
theorem zetaCompletedPacketNormSq_nonnegative (f : ZetaAdmissibleFunction) :
    ∀ B : ℝ, 0 ≤ zetaCompletedPacketNormSq f B := by
  intro B
  unfold zetaCompletedPacketNormSq
  exact ZetaPacketEnsemble.normSq_nonneg (zetaPacketAsEnsemble f B)

/-- The reconstructed packet decomposes into prime, archimedean, and correction parts. -/
theorem zetaPacketAsEnsemble_decomposition (f : ZetaAdmissibleFunction) :
    ∀ B : ℝ, zetaPacketAsEnsemble f B =
      zetaPrimePacketAsEnsemble f B +
        zetaArchimedeanPacketAsEnsemble f +
        zetaCorrectionPacketAsEnsemble f := by
  intro B
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
