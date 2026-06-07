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

open Classical

namespace ZetaPacketEnsemble

/-- The packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (a : ℝ) : ZetaPacketEnsemble :=
  Finsupp.single ℓ a

end ZetaPacketEnsemble

namespace ZetaAdmissibleFunction

/-- The canonical logarithmic support radius extracted from compact support. -/
noncomputable def zetaPacketSupportRadius (f : ZetaAdmissibleFunction) : ℝ :=
  Classical.choose <| by
    have hcomp : IsCompact (tsupport f.toZetaTestFunction) := by
      simpa [HasCompactSupport, tsupport] using f.toZetaTestFunction.hasCompactSupport
    rcases IsCompact.bddAbove hcomp with ⟨B, hB⟩
    exact ⟨B, hB⟩

theorem zetaPacketSupportRadius_spec (f : ZetaAdmissibleFunction) :
    ∀ x ∈ tsupport f.toZetaTestFunction, x ≤ zetaPacketSupportRadius f := by
  classical
  unfold zetaPacketSupportRadius
  exact Classical.choose_spec <| by
    have hcomp : IsCompact (tsupport f.toZetaTestFunction) := by
      simpa [HasCompactSupport, tsupport] using f.toZetaTestFunction.hasCompactSupport
    rcases IsCompact.bddAbove hcomp with ⟨B, hB⟩
    exact ⟨B, hB⟩

/-- The prime packet weight on a prime-power label. -/
def zetaPrimePacketWeight : ZetaPacketLabel → ℝ
  | .prime p m =>
      if hp : Nat.Prime p then
        Real.log p / Real.sqrt (p ^ m)
      else
        0
  | _ => 0

theorem zetaPrimePacketWeight_prime (p m : ℕ) (hp : Nat.Prime p) :
    zetaPrimePacketWeight (.prime p m) = Real.log p / Real.sqrt (p ^ m) := by
  simp [zetaPrimePacketWeight, hp]

theorem zetaPrimePacketWeight_nonprime (ℓ : ZetaPacketLabel) (h : ¬ ∃ p m, ℓ = .prime p m) :
    zetaPrimePacketWeight ℓ = 0 := by
  cases ℓ with
  | prime p m =>
      exfalso
      apply h
      exact ⟨p, m, rfl⟩
  | archimedean =>
      simp [zetaPrimePacketWeight]
  | correction =>
      simp [zetaPrimePacketWeight]

/-- The finite set of prime-power indices used by the prime-side reconstruction. -/
noncomputable def zetaPacketPrimeSupport (f : ZetaAdmissibleFunction) : Finset (ℕ × ℕ) :=
  Finset.product
    (Finset.range (Nat.ceil (Real.exp (zetaPacketSupportRadius f)) + 1))
    (Finset.range (Nat.ceil (Real.exp (zetaPacketSupportRadius f)) + 1))

/-- The prime packet associated to an admissible function. -/
noncomputable def zetaPrimePacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ∑ ℓ in zetaPacketPrimeSupport f,
    ZetaPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (Complex.re
        (zetaPrimePacketWeight (ZetaPacketLabel.prime ℓ.1 ℓ.2) •
          ZetaTestFunction.primePacketTranslationDefect ℓ.1 ℓ.2 f.toZetaTestFunction' 0))

/-- The archimedean packet associated to an admissible function. -/
noncomputable def zetaArchimedeanPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .archimedean
    (Complex.re (ZetaTestFunction.archimedeanTranslationDefect 0 f.toZetaTestFunction' 0))

/-- The completion/correction packet associated to an admissible function. -/
noncomputable def zetaCorrectionPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .correction (Complex.re (zetaCompletionCorrection 0))

/-- The canonical completed zeta packet attached to an admissible probe. -/
noncomputable def zetaPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaPrimePacketAsEnsemble f +
    zetaArchimedeanPacketAsEnsemble f +
    zetaCorrectionPacketAsEnsemble f

/-- The packet is finite-support because it is a finite sum of singletons. -/
theorem zetaPacketAsEnsemble_finiteSupport (f : ZetaAdmissibleFunction) :
    Finite ((zetaPacketAsEnsemble f).support : Set ZetaPacketLabel) := by
  exact Set.toFinite ((zetaPacketAsEnsemble f).support : Set ZetaPacketLabel)

/-- The packet norm-square of the reconstructed packet. -/
noncomputable def zetaCompletedPacketNormSq (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPacketEnsemble.normSq (zetaPacketAsEnsemble f)

/-- The reconstructed packet norm-square is nonnegative. -/
theorem zetaCompletedPacketNormSq_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPacketNormSq f := by
  unfold zetaCompletedPacketNormSq
  exact ZetaPacketEnsemble.normSq_nonneg (zetaPacketAsEnsemble f)

/-- The reconstructed packet decomposes into prime, archimedean, and correction parts. -/
theorem zetaPacketAsEnsemble_decomposition (f : ZetaAdmissibleFunction) :
    zetaPacketAsEnsemble f =
      zetaPrimePacketAsEnsemble f +
        zetaArchimedeanPacketAsEnsemble f +
        zetaCorrectionPacketAsEnsemble f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
