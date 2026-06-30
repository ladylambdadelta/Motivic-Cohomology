import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.N_TwoMovingLogWindowDecomposition

/-!
# Oriented moving-log branch-wall assembly

This file owns the final BinetKernel-facing transport from the oriented
plus/minus moving logarithmic spike estimates to finite-height lower-vertical
decay.  The remaining analytic input is the oriented real weighted-log
estimate; this file only assembles already-owned kernel accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- The standard Binet decaying-tail integral is invariant under complex
conjugation. -/
theorem Complex.binetSecondFormulaDecayingTailIntegral_conj
    (w : ℂ) :
    Complex.binetSecondFormulaDecayingTailIntegral ((starRingEnd ℂ) w) =
      Complex.binetSecondFormulaDecayingTailIntegral w := by
  have hnorm : ‖(starRingEnd ℂ) w‖ = ‖w‖ :=
    RCLike.norm_conj w
  calc
    Complex.binetSecondFormulaDecayingTailIntegral ((starRingEnd ℂ) w) =
        ∫ t : ℝ in Set.Ioi (‖(starRingEnd ℂ) w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      rfl
    _ =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      exact congrArg
        (fun x : ℝ =>
          ∫ t : ℝ in Set.Ioi (x / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        hnorm
    _ = Complex.binetSecondFormulaDecayingTailIntegral w := by
      rfl

/-- The plus oriented moving-log spike is the conjugate-reflection of the
minus oriented moving-log spike. -/
theorem Complex.binetSecondFormula_plusMovingLog_oriented_scaled_decay_of_minus
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cplus : ℝ,
      0 < Cplus ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cplus / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hminus with
  | ⟨Cminus, hCminus_pos, hminus_bound⟩ =>
      exact
        ⟨Cminus, hCminus_pos,
          fun w hw_re_pos hw_large =>
            let wc : ℂ := (starRingEnd ℂ) w
            let Aplus : ℝ → ℝ := fun t : ℝ =>
              (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let BminusConj : ℝ → ℝ := fun t : ℝ =>
              (2 * Real.log ((3 * ‖wc‖) / max wc.re |wc.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
            let Sc : Set ℝ := Set.Ioc (‖wc‖ / 2) (2 * ‖wc‖)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            let Jc : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral wc
            have hnorm : ‖wc‖ = ‖w‖ :=
              RCLike.norm_conj w
            have hre : wc.re = w.re :=
              Complex.conj_re w
            have him : wc.im = -w.im :=
              Complex.conj_im w
            have hwc_re_pos : 0 < wc.re :=
              Eq.subst
                (motive := fun x : ℝ => 0 < x)
                hre.symm
                hw_re_pos
            have hwc_large : 2 ≤ ‖wc‖ :=
              Eq.subst
                (motive := fun x : ℝ => 2 ≤ x)
                hnorm.symm
                hw_large
            have hraw :
                2 * ∫ t : ℝ in Sc, BminusConj t ≤
                  (Cminus / ‖wc‖) * Jc :=
              hminus_bound wc hwc_re_pos hwc_large
            have hset :
                Sc = S := by
              exact congrArg₂
                (fun left right : ℝ => Set.Ioc (left / 2) (2 * right))
                hnorm hnorm
            have hj :
                Jc = J :=
              Complex.binetSecondFormulaDecayingTailIntegral_conj w
            have hrhs :
                (Cminus / ‖wc‖) * Jc =
                  (Cminus / ‖w‖) * J := by
              exact congrArg₂
                (fun x y : ℝ => x * y)
                (congrArg (fun x : ℝ => Cminus / x) hnorm)
                hj
            have hpoint :
                ∀ t : ℝ, BminusConj t = Aplus t := by
              intro t
              have hdist :
                  |wc.im - t| = |w.im + t| := by
                calc
                  |wc.im - t| = |(-w.im) - t| := by
                    exact congrArg (fun x : ℝ => |x - t|) him
                  _ = |-(w.im + t)| := by
                    exact congrArg abs
                      (calc
                        (-w.im) - t = (-w.im) + -t := by
                          exact sub_eq_add_neg (-w.im) t
                        _ = -(w.im + t) := by
                          exact (neg_add w.im t).symm)
                  _ = |w.im + t| := by
                    exact abs_neg (w.im + t)
              have hmax :
                  max wc.re |wc.im - t| =
                    max w.re |w.im + t| :=
                congrArg₂ max hre hdist
              have hnum :
                  3 * ‖wc‖ = 3 * ‖w‖ :=
                congrArg (fun x : ℝ => 3 * x) hnorm
              let A : ℝ := max w.re |w.im + t|
              let B : ℝ := 3 * ‖w‖
              have harg :
                  (3 * ‖wc‖) / max wc.re |wc.im - t| =
                    (A / B)⁻¹ := by
                calc
                  (3 * ‖wc‖) / max wc.re |wc.im - t| =
                      B / A := by
                    exact congrArg₂ (fun x y : ℝ => x / y) hnum hmax
                  _ = (A / B)⁻¹ := by
                    exact (inv_div A B).symm
              have hlog :
                  Real.log ((3 * ‖wc‖) / max wc.re |wc.im - t|) =
                    -Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)) := by
                calc
                  Real.log ((3 * ‖wc‖) / max wc.re |wc.im - t|) =
                      Real.log ((A / B)⁻¹) := by
                    exact congrArg Real.log harg
                  _ = -Real.log (A / B) := by
                    exact Real.log_inv (A / B)
              exact congrArg
                (fun x : ℝ => (2 * x) / Real.exp ((2 : ℝ) * Real.pi * t))
                hlog
            have hintegral_eq :
                ∫ t : ℝ in Sc, BminusConj t =
                  ∫ t : ℝ in S, Aplus t := by
              calc
                ∫ t : ℝ in Sc, BminusConj t =
                    ∫ t : ℝ in S, BminusConj t := by
                  exact congrArg (fun U : Set ℝ => ∫ t : ℝ in U, BminusConj t) hset
                _ = ∫ t : ℝ in S, Aplus t := by
                  exact setIntegral_congr_fun measurableSet_Ioc
                    (fun t _ht => hpoint t)
            have htwice_eq :
                2 * ∫ t : ℝ in Sc, BminusConj t =
                  2 * ∫ t : ℝ in S, Aplus t :=
              congrArg (fun x : ℝ => 2 * x) hintegral_eq
            have hleft :
                2 * ∫ t : ℝ in S, Aplus t ≤
                  (Cminus / ‖wc‖) * Jc :=
              Eq.subst
                (motive := fun x : ℝ =>
                  x ≤ (Cminus / ‖wc‖) * Jc)
                htwice_eq
                hraw
            Eq.subst
              (motive := fun x : ℝ =>
                2 * ∫ t : ℝ in S, Aplus t ≤ x)
              hrhs
              hleft⟩

/-- Finite-height lower-vertical decay follows from the oriented plus and
minus moving-log spike estimates. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_oriented_plus_minus
    (hplus :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w)
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have htwoMoving :
      ∃ Ctwo : ℝ,
        0 < Ctwo ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max
                    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Ctwo / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_twoMovingLogWindow_scaled_decay_of_oriented_plus_minus
      hplus hminus
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_twoMovingLogWindow_decay
      htwoMoving

/-- Finite-height lower-vertical decay follows from the single oriented
minus moving-log spike estimate; the plus estimate is its conjugate-reflection
transport. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_oriented_minus
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have hplus :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_plusMovingLog_oriented_scaled_decay_of_minus
      hminus
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_oriented_plus_minus
      hplus hminus

end

end LFunctions
end Boundary
