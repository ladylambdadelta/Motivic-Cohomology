import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.Owner

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

/-- Helper: -2(N+1) ≤ -N. Shows exponent sum for rapid decay. -/
private lemma neg_sum_le_neg_nat (N : ℕ) :
    (-(N + 1 : ℤ)) + (-(N + 1 : ℤ)) ≤ -(N : ℤ) := by
  have h1 : (-(N + 1 : ℤ)) + (-(N + 1 : ℤ)) = -(2 * N + 2 : ℤ) := by
    calc (-(N + 1 : ℤ)) + (-(N + 1 : ℤ))
        = -(N + 1) - (N + 1) := by exact Int.add_eq_sub_of_neg_right (Int.neg_add_eq_sub _ _).symm
      _ = -(N + 1 + (N + 1)) := by exact Int.sub_eq_neg_add (N + 1) (N + 1)
      _ = -(2 * N + 2) := by norm_num
  rw [h1]
  have h2 : (2 : ℤ) * N + 2 ≥ N := by
    have : (0 : ℤ) ≤ N + 2 := by exact Int.add_nonneg (Int.coe_nat_nonneg N) (by norm_num : (0 : ℤ) ≤ 2)
    exact by norm_num
  exact Int.neg_le_neg h2

/-- Helper: N - (2N + 1) ≤ -N. Mixed exponent inequality. -/
private lemma mixed_exp_le_neg_nat (N : ℕ) :
    (N : ℤ) + (-(N + N + 1 : ℤ)) ≤ -(N : ℤ) := by
  have h1 : (N : ℤ) + (-(N + N + 1 : ℤ)) = -(N + 1 : ℤ) := by norm_num
  rw [h1]
  have h2 : (N + 1 : ℤ) ≥ 0 := Int.add_nonneg (Int.coe_nat_nonneg N) (by norm_num : (0 : ℤ) ≤ 1)
  exact Int.neg_le_neg h2

/-- Helper: K - (K + N + 1) ≤ -N. Polynomial degree exponent. -/
private lemma poly_deg_exp_le_neg_nat (K N : ℕ) :
    (K : ℤ) + (-(K + N + 1 : ℤ)) ≤ -(N : ℤ) := by
  have h1 : (K : ℤ) + (-(K + N + 1 : ℤ)) = -(N + 1 : ℤ) := by norm_num
  rw [h1]
  have h2 : (N + 1 : ℤ) ≥ 0 := Int.add_nonneg (Int.coe_nat_nonneg N) (by norm_num : (0 : ℤ) ≤ 1)
  exact Int.neg_le_neg h2

/-- Real power bookkeeping for multiplying two rapidly decaying faces. -/
theorem rapidTimesRapidPower_le_requestedRapidPower
    (N : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)) ≤
      X ^ (-(N : ℤ)) := by
  have hX_ne_zero : X ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hX)
  have hexp :
      (-(N + 1 : ℤ)) + (-(N + 1 : ℤ)) ≤ -(N : ℤ) :=
    neg_sum_le_neg_nat N
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
      (N : ℤ) + (-(N + N + 1 : ℤ)) ≤ -(N : ℤ) :=
    mixed_exp_le_neg_nat N
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
      (K : ℤ) + (-(K + N + 1 : ℤ)) ≤ -(N : ℤ) :=
    poly_deg_exp_le_neg_nat K N
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
