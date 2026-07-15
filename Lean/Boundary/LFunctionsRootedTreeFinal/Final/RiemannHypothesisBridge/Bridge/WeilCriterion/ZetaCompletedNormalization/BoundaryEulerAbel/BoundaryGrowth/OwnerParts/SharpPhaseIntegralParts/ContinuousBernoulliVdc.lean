import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.Part03_TaylorBlockSplit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.CombinedBound

/-!
# Continuous Bernoulli logarithmic-phase estimate

This file owns the continuous oscillatory estimate for
`B_1(x) x^{-it}` on the canonical post-cutoff interval.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Exact coefficient form of the Taylor-linear Bernoulli block sum.

The unit first-moment theorem turns each linear integral into the derivative
coefficient at the left endpoint multiplied by `1/12`; the remaining object is a
finite reciprocal-weighted logarithmic phase sum. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_linearBlockSum_eq_momentCoefficientSum
    (t : ℝ)
    {K : ℕ} :
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
        t K =
      (1 / 12 : ℂ) *
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          (((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) := by
  let C : ℕ → ℂ := fun n =>
    (((-(t : ℂ) * Complex.I) /
        (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))))
  have hlocal :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (C n *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) =
          (1 / 12 : ℂ) * C n := by
    intro n hn
    let m : ℕ := n - 1
    let s : Set ℝ := Set.Ioc (((m : ℕ) : ℝ)) (((n : ℕ) : ℝ))
    let B : ℝ → ℂ := fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
    let X : ℝ → ℂ := fun x =>
      (((x - ((m : ℕ) : ℝ) : ℝ) : ℂ))
    have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
      (Finset.mem_Ioc.mp hn).1
    have hn_pos : 0 < n :=
      lt_of_le_of_lt (Nat.zero_le ⌊2 + ‖t‖⌋₊) hcutoff_lt_n
    have hm_succ : m + 1 = n := by
      exact Nat.succ_pred_eq_of_pos hn_pos
    have hupper :
        (((m + 1 : ℕ) : ℝ)) = (((n : ℕ) : ℝ)) := by
      exact congrArg Nat.cast hm_succ
    have hmoment :
        (∫ x in Set.Ioc (((m : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          B x * X x) = (1 / 12 : ℂ) := by
      exact Eq.subst
        (motive := fun r : ℝ =>
          (∫ x in Set.Ioc (((m : ℕ) : ℝ)) r, B x * X x) =
            (1 / 12 : ℂ))
        hupper
        (eulerMaclaurinFirstPeriodicBernoulli_oneInterval_firstMoment_eq_one_twelfth
          m)
    have hpoint :
        (fun x : ℝ =>
          B x * (C n * ((x : ℂ) - (((m : ℕ) : ℝ) : ℂ)))) =
          fun x : ℝ => C n * (B x * X x) := by
      funext x
      have hx_sub :
          ((x : ℂ) - (((m : ℕ) : ℝ) : ℂ)) = X x := by
        calc
          ((x : ℂ) - (((m : ℕ) : ℝ) : ℂ)) =
              (((x : ℝ) : ℂ) - (((m : ℕ) : ℝ) : ℂ)) := rfl
          _ = (((x - ((m : ℕ) : ℝ) : ℝ) : ℂ)) := by
            exact (Complex.ofReal_sub x (((m : ℕ) : ℝ))).symm
      calc
        B x * (C n * ((x : ℂ) - (((m : ℕ) : ℝ) : ℂ))) =
            B x * (C n * X x) := by
          exact congrArg (fun z : ℂ => B x * (C n * z)) hx_sub
        _ = C n * (B x * X x) := by
          exact Eq.trans
            (mul_assoc (B x) (C n) (X x)).symm
            (congrArg (fun z : ℂ => z * X x) (mul_comm (B x) (C n))
              |>.trans (mul_assoc (C n) (B x) (X x)))
    have hintegral :
        (∫ x in s, B x * (C n * ((x : ℂ) - (((m : ℕ) : ℝ) : ℂ)))) =
          ∫ x in s, C n * (B x * X x) := by
      exact congrArg (fun G : ℝ → ℂ => ∫ x in s, G x) hpoint
    have hconst :
        (∫ x in s, C n * (B x * X x)) =
          C n * ∫ x in s, B x * X x :=
      MeasureTheory.integral_mul_left (C n) (fun x : ℝ => B x * X x)
    calc
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (C n *
            ((x : ℂ) -
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) =
          C n * ∫ x in s, B x * X x := by
        exact Eq.trans hintegral hconst
      _ = C n * (1 / 12 : ℂ) := by
        exact congrArg (fun z : ℂ => C n * z) hmoment
      _ = (1 / 12 : ℂ) * C n := by
        exact mul_comm (C n) (1 / 12 : ℂ)
  have hsum :
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
          t K =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, (1 / 12 : ℂ) * C n := by
    have hdefinition :
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
            t K =
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
            ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (C n *
                  ((x : ℂ) -
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))) := rfl
    exact Eq.trans hdefinition (Finset.sum_congr rfl hlocal)
  calc
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinearBlockSum
        t K =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, (1 / 12 : ℂ) * C n :=
      hsum
    _ =
        (1 / 12 : ℂ) *
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, C n := by
      exact (Finset.mul_sum (Finset.Ioc ⌊2 + ‖t‖⌋₊ K)
        (fun n : ℕ => C n) (1 / 12 : ℂ)).symm

/-- Combined sharp block estimate for the Bernoulli-weighted logarithmic phase.

The proof is owned at the combined zero-mean level: the Taylor decomposition is
available above, but the sharp constant is not obtained from separately sharp
absolute estimates for the Taylor-linear and Taylor-remainder pieces. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_combined
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  have hglobal :=
    norm_boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_le_postCutoffScale
      t ht hK
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
    (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
      t).symm
    hglobal

/-- Continuous van der Corput estimate for the first-periodic Bernoulli amplitude
against the logarithmic phase after the canonical cutoff.

This is the analytic primitive behind the sharp phase-integral layer.  The proof
is the classical bounded-periodic-amplitude argument for `B_1(x) exp(-it log x)`:
split into unit intervals, use the zero mean of `B_1`, integrate the Taylor-linear
coefficient by Abel/Dirichlet summation, and bound the quadratic Taylor remainder
by the inverse-square post-cutoff majorant. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_continuousVdc_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  have hblocks :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_combined
      t ht hK
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t)
      hblocks

end
end LFunctions
end Boundary
