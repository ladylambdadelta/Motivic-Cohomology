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
  have hN_le_N_add_one :
      (N : ℤ) ≤ (N : ℤ) + 1 := by
    calc
      (N : ℤ) = (N : ℤ) + 0 := (add_zero (N : ℤ)).symm
      _ ≤ (N : ℤ) + 1 := add_le_add_left zero_le_one (N : ℤ)
  have hN_add_one_nonnegative :
      0 ≤ (N : ℤ) + 1 :=
    Int.add_nonneg (Int.natCast_nonneg N) zero_le_one
  have hN_add_one_le_double :
      (N : ℤ) + 1 ≤ ((N : ℤ) + 1) + ((N : ℤ) + 1) := by
    calc
      (N : ℤ) + 1 = ((N : ℤ) + 1) + 0 := (add_zero ((N : ℤ) + 1)).symm
      _ ≤ ((N : ℤ) + 1) + ((N : ℤ) + 1) :=
        add_le_add_left hN_add_one_nonnegative ((N : ℤ) + 1)
  have hN_le_double :
      (N : ℤ) ≤ ((N : ℤ) + 1) + ((N : ℤ) + 1) :=
    le_trans hN_le_N_add_one hN_add_one_le_double
  calc
    (-(N + 1 : ℤ)) + (-(N + 1 : ℤ))
        = -(((N : ℤ) + 1) + ((N : ℤ) + 1)) := by
          change -((N : ℤ) + 1) + -((N : ℤ) + 1) =
            -(((N : ℤ) + 1) + ((N : ℤ) + 1))
          exact (neg_add ((N : ℤ) + 1) ((N : ℤ) + 1)).symm
    _ ≤ -(N : ℤ) := Int.neg_le_neg hN_le_double

/-- Helper: N - (2N + 1) ≤ -N. Mixed exponent inequality. -/
private lemma mixed_exp_le_neg_nat (N : ℕ) :
    (N : ℤ) + (-(N + N + 1 : ℤ)) ≤ -(N : ℤ) := by
  have hidentity :
      (N : ℤ) + (-(N + N + 1 : ℤ)) = -((N : ℤ) + 1) := by
    change
      (N : ℤ) + -(((N : ℤ) + (N : ℤ)) + 1) =
        -((N : ℤ) + 1)
    calc
      (N : ℤ) + -(((N : ℤ) + (N : ℤ)) + 1)
          = (N : ℤ) + (-((N : ℤ) + (N : ℤ)) + -1) := by
            exact congrArg (fun x : ℤ => (N : ℤ) + x)
              (neg_add ((N : ℤ) + (N : ℤ)) 1)
      _ = (N : ℤ) + ((-(N : ℤ) + -(N : ℤ)) + -1) := by
        exact congrArg
          (fun x : ℤ => (N : ℤ) + (x + -1))
          (neg_add (N : ℤ) (N : ℤ))
      _ = (N : ℤ) + (-(N : ℤ) + (-(N : ℤ) + -1)) := by
        exact congrArg
          (fun x : ℤ => (N : ℤ) + x)
          (add_assoc (-(N : ℤ)) (-(N : ℤ)) (-1))
      _ = ((N : ℤ) + -(N : ℤ)) + (-(N : ℤ) + -1) := by
        exact (add_assoc (N : ℤ) (-(N : ℤ)) (-(N : ℤ) + -1)).symm
      _ = 0 + (-(N : ℤ) + -1) := by
        exact congrArg (fun x : ℤ => x + (-(N : ℤ) + -1))
          (add_neg_cancel (N : ℤ))
      _ = -(N : ℤ) + -1 := zero_add (-(N : ℤ) + -1)
      _ = -((N : ℤ) + 1) := (neg_add (N : ℤ) 1).symm
  have hnonnegative :
      0 ≤ (N : ℤ) + 1 :=
    Int.add_nonneg (Int.natCast_nonneg N) zero_le_one
  have hneg_le : -((N : ℤ) + 1) ≤ -(N : ℤ) :=
    Int.neg_le_neg
      (calc
        (N : ℤ) = (N : ℤ) + 0 := (add_zero (N : ℤ)).symm
        _ ≤ (N : ℤ) + 1 := add_le_add_left zero_le_one (N : ℤ))
  exact Eq.subst
    (motive := fun x : ℤ => x ≤ -(N : ℤ))
    hidentity.symm
    hneg_le

/-- Helper: K - (K + N + 1) ≤ -N. Polynomial degree exponent. -/
private lemma poly_deg_exp_le_neg_nat (K N : ℕ) :
    (K : ℤ) + (-(K + N + 1 : ℤ)) ≤ -(N : ℤ) := by
  have hidentity :
      (K : ℤ) + (-(K + N + 1 : ℤ)) = -((N : ℤ) + 1) := by
    change
      (K : ℤ) + -(((K : ℤ) + (N : ℤ)) + 1) =
        -((N : ℤ) + 1)
    calc
      (K : ℤ) + -(((K : ℤ) + (N : ℤ)) + 1)
          = (K : ℤ) + (-((K : ℤ) + (N : ℤ)) + -1) := by
            exact congrArg (fun x : ℤ => (K : ℤ) + x)
              (neg_add ((K : ℤ) + (N : ℤ)) 1)
      _ = (K : ℤ) + ((-(K : ℤ) + -(N : ℤ)) + -1) := by
        exact congrArg
          (fun x : ℤ => (K : ℤ) + (x + -1))
          (neg_add (K : ℤ) (N : ℤ))
      _ = (K : ℤ) + (-(K : ℤ) + (-(N : ℤ) + -1)) := by
        exact congrArg
          (fun x : ℤ => (K : ℤ) + x)
          (add_assoc (-(K : ℤ)) (-(N : ℤ)) (-1))
      _ = ((K : ℤ) + -(K : ℤ)) + (-(N : ℤ) + -1) := by
        exact (add_assoc (K : ℤ) (-(K : ℤ)) (-(N : ℤ) + -1)).symm
      _ = 0 + (-(N : ℤ) + -1) := by
        exact congrArg (fun x : ℤ => x + (-(N : ℤ) + -1))
          (add_neg_cancel (K : ℤ))
      _ = -(N : ℤ) + -1 := zero_add (-(N : ℤ) + -1)
      _ = -((N : ℤ) + 1) := (neg_add (N : ℤ) 1).symm
  have hneg_le : -((N : ℤ) + 1) ≤ -(N : ℤ) :=
    Int.neg_le_neg
      (calc
        (N : ℤ) = (N : ℤ) + 0 := (add_zero (N : ℤ)).symm
        _ ≤ (N : ℤ) + 1 := add_le_add_left zero_le_one (N : ℤ))
  exact Eq.subst
    (motive := fun x : ℤ => x ≤ -(N : ℤ))
    hidentity.symm
    hneg_le

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
against sufficiently rapid decay to reach the requested decay order `N`. -/
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
