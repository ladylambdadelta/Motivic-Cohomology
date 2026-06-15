import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPacketLabels.Owner

/-!
# Boundary zeta packet coefficients

This file attaches concrete coefficients to the packet labels from the
centered additive-line normalization. The coefficients are intentionally
primitive: the later packet transform and Gram layers should consume these
formulae directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Real Complex

/-- The coefficient attached to a zeta packet label. -/
def zetaPacketCoeff : ZetaPacketLabel → ℝ
  | .prime m n => zetaPrimePacketCenter (m + 1 : ℝ) n
  | .archimedean => 0
  | .correction => 0

theorem zetaPacketCoeff_prime (m n : ℕ) :
    zetaPacketCoeff (.prime m n) = zetaPrimePacketCenter (m + 1 : ℝ) n := rfl

theorem zetaPacketCoeff_archimedean :
    zetaPacketCoeff .archimedean = 0 := rfl

theorem zetaPacketCoeff_correction :
    zetaPacketCoeff .correction = 0 := rfl

theorem zetaPacketCoeff_dual (ℓ : ZetaPacketLabel) :
    zetaPacketCoeff (ZetaPacketLabel.dual ℓ) = zetaPacketCoeff ℓ := by
  cases ℓ <;> rfl

/-- Reflection compatibility for the packet coefficient function. -/
theorem zetaPacketCoeff_reflectionCompat (ℓ : ZetaPacketLabel) :
    zetaPacketCoeff (ZetaPacketLabel.dual ℓ) = zetaPacketCoeff ℓ := by
  exact zetaPacketCoeff_dual ℓ

/-- Centering compatibility for the prime packet coefficients. -/
theorem zetaPacketCoeff_centering (m n : ℕ) :
    zetaPacketCoeff (.prime m n) = zetaPrimePacketCenter (m + 1 : ℝ) n := by
  rfl

/-- Normalization compatibility for the packet coefficients. -/
theorem zetaPacketCoeff_normalization (ℓ : ZetaPacketLabel) :
    zetaPacketCoeff ℓ =
      match ℓ with
      | .prime m n => zetaPrimePacketCenter (m + 1 : ℝ) n
      | .archimedean => 0
      | .correction => 0 := by
  cases ℓ <;> rfl

theorem zetaPacketCoeff_prime_succ (m n : ℕ) :
    zetaPacketCoeff (.prime m (n + 1)) =
      zetaPacketCoeff (.prime m n) + Real.log (m + 1 : ℝ) := by
  have hn_succ_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 :=
    Eq.trans
      (Nat.cast_add n 1)
      (congrArg (fun x : ℝ => (n : ℝ) + x) Nat.cast_one)
  calc
    zetaPacketCoeff (.prime m (n + 1)) =
        zetaPrimePacketCenter (m + 1 : ℝ) ((n + 1 : ℕ) : ℝ) :=
      zetaPacketCoeff_prime m (n + 1)
    _ = zetaPrimePacketCenter (m + 1 : ℝ) ((n : ℝ) + 1) :=
      congrArg
        (fun x : ℝ => zetaPrimePacketCenter (m + 1 : ℝ) x)
        hn_succ_cast
    _ = zetaPrimePacketCenter (m + 1 : ℝ) n + Real.log (m + 1 : ℝ) :=
      zetaPrimePacketCenter_succ (p := (m + 1 : ℝ)) n
    _ = zetaPacketCoeff (.prime m n) + Real.log (m + 1 : ℝ) :=
      congrArg
        (fun x : ℝ => x + Real.log (m + 1 : ℝ))
        (zetaPacketCoeff_prime m n).symm

end

end LFunctions
end Boundary
