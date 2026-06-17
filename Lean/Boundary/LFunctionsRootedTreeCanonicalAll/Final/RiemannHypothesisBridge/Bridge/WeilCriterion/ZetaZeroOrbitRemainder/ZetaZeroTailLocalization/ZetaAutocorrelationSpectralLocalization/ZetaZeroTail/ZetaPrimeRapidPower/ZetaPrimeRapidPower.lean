import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeTwoFaceCoordinates

/-!
# Prime rapid-power bookkeeping

This file owns the integer-exponent bookkeeping used by the rapid-decay product
estimates in completed prime analytic control.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Real power bookkeeping for multiplying two rapidly decaying faces. -/
theorem rapidTimesRapidPower_le_requestedRapidPower
    (N : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)) ≤
      X ^ (-(N : ℤ)) := by
  have hX_ne_zero : X ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hX)
  have hexp :
      (-(N + 1 : ℤ)) + (-(N + 1 : ℤ)) ≤ -(N : ℤ) := by
    omega
  have hcombine :
      X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)) =
        X ^ ((-(N + 1 : ℤ)) + (-(N + 1 : ℤ))) := by
    exact (zpow_add₀ hX_ne_zero (-(N + 1 : ℤ)) (-(N + 1 : ℤ))).symm
  have hmono :
      X ^ ((-(N + 1 : ℤ)) + (-(N + 1 : ℤ))) ≤
        X ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ hX hexp
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ X ^ (-(N : ℤ)))
    hcombine.symm
    hmono

/-- Real power bookkeeping for the strip product estimate. -/
theorem polynomialTimesRapidPower_le_requestedRapidPower
    (N : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    X ^ N * X ^ (-(N + N + 1 : ℤ)) ≤
      X ^ (-(N : ℤ)) := by
  have hX_ne_zero : X ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hX)
  have hexp :
      (N : ℤ) + (-(N + N + 1 : ℤ)) ≤ -(N : ℤ) := by
    omega
  have hnat :
      X ^ N = X ^ (N : ℤ) := by
    exact (zpow_natCast X N).symm
  have hcombine :
      X ^ N * X ^ (-(N + N + 1 : ℤ)) =
        X ^ ((N : ℤ) + (-(N + N + 1 : ℤ))) := by
    calc
      X ^ N * X ^ (-(N + N + 1 : ℤ)) =
          X ^ (N : ℤ) * X ^ (-(N + N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(N + N + 1 : ℤ)))
          hnat
      _ = X ^ ((N : ℤ) + (-(N + N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_ne_zero (N : ℤ) (-(N + N + 1 : ℤ))).symm
  have hmono :
      X ^ ((N : ℤ) + (-(N + N + 1 : ℤ))) ≤
        X ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ hX hexp
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ X ^ (-(N : ℤ)))
    hcombine.symm
    hmono

/-- Real power bookkeeping for multiplying an independent polynomial-growth degree `K`
by sufficiently rapid decay to obtain the requested decay order `N`. -/
theorem polynomialDegreeTimesRapidPower_le_requestedRapidPower
    (K N : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    X ^ K * X ^ (-(K + N + 1 : ℤ)) ≤
      X ^ (-(N : ℤ)) := by
  have hX_ne_zero : X ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hX)
  have hexp :
      (K : ℤ) + (-(K + N + 1 : ℤ)) ≤ -(N : ℤ) := by
    omega
  have hnat :
      X ^ K = X ^ (K : ℤ) := by
    exact (zpow_natCast X K).symm
  have hcombine :
      X ^ K * X ^ (-(K + N + 1 : ℤ)) =
        X ^ ((K : ℤ) + (-(K + N + 1 : ℤ))) := by
    calc
      X ^ K * X ^ (-(K + N + 1 : ℤ)) =
          X ^ (K : ℤ) * X ^ (-(K + N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(K + N + 1 : ℤ)))
          hnat
      _ = X ^ ((K : ℤ) + (-(K + N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_ne_zero (K : ℤ) (-(K + N + 1 : ℤ))).symm
  have hmono :
      X ^ ((K : ℤ) + (-(K + N + 1 : ℤ))) ≤
        X ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ hX hexp
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ X ^ (-(N : ℤ)))
    hcombine.symm
    hmono

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
