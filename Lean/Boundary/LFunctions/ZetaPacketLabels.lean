import Boundary.LFunctions.ZetaCenteredNormalization

/-!
# Boundary zeta packet labels

This file isolates the label algebra for the explicit-formula packet route.
The labels themselves are elementary, but they are the owner-level objects that
later packet-coefficient and reflection lemmas will consume.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The three packet families in the centered explicit-formula decomposition. -/
inductive ZetaPacketLabel where
  | prime : ℕ → ℕ → ZetaPacketLabel
  | archimedean : ZetaPacketLabel
  | correction : ZetaPacketLabel
deriving DecidableEq, Repr

namespace ZetaPacketLabel

/-- Swap the prime-power indices. This is the label-level reflection on primes. -/
def swapPrimeIndices : ZetaPacketLabel → ZetaPacketLabel
  | prime m n => prime n m
  | archimedean => archimedean
  | correction => correction

/-- The dual label induced by the centered functional equation symmetry. -/
def dual : ZetaPacketLabel → ZetaPacketLabel
  | prime m n => prime m n
  | archimedean => archimedean
  | correction => correction

theorem swapPrimeIndices_prime (m n : ℕ) :
    swapPrimeIndices (prime m n) = prime n m := rfl

theorem swapPrimeIndices_archimedean :
    swapPrimeIndices archimedean = archimedean := rfl

theorem swapPrimeIndices_correction :
    swapPrimeIndices correction = correction := rfl

theorem dual_prime (m n : ℕ) : dual (prime m n) = prime m n := rfl

theorem dual_archimedean : dual archimedean = archimedean := rfl

theorem dual_correction : dual correction = correction := rfl

theorem dual_dual (ℓ : ZetaPacketLabel) : dual (dual ℓ) = ℓ := by
  cases ℓ <;> rfl

theorem swapPrimeIndices_swapPrimeIndices (ℓ : ZetaPacketLabel) :
    swapPrimeIndices (swapPrimeIndices ℓ) = ℓ := by
  cases ℓ <;> rfl

theorem dual_swapPrimeIndices (ℓ : ZetaPacketLabel) :
    dual (swapPrimeIndices ℓ) = swapPrimeIndices (dual ℓ) := by
  cases ℓ <;> rfl

end ZetaPacketLabel

end
end LFunctions
end Boundary
