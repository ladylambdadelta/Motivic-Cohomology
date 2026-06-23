import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.HalfPlaneTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.OneIntervalBernoulli
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FiniteIntervalAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.LocalMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.ParameterDerivativeMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffBernoulliHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripTopology
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PostCutoffTail

/-!
The analytic pole-cleared Euler-Maclaurin layer below the half-plane continuation
lemmas.  This file owns the removable-value transport and the first-order
half-open band formulas used by the pole-cleared boundary normalization layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- Multiplication by `s - 1` transports the raw non-pole
Euler-Maclaurin formula to the existing pole-cleared term definitions. -/
theorem eulerMaclaurin_poleCleared_formula_of_raw_formula
    {z : ℂ}
    (hz_ne_one : z ≠ 1)
    (hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  let a : ℂ := z - 1
  let F : ℂ := eulerMaclaurinZetaFinitePart z
  let M : ℂ := eulerMaclaurinZetaMainTerm z
  let E : ℂ := eulerMaclaurinZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinZetaBernoulliIntegralRemainder z
  have hpole :
      poleClearedRiemannZeta z = a * riemannZeta z := by
    exact poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hraw_local : riemannZeta z = F + M + E + R :=
    hraw
  have hmul_raw :
      a * riemannZeta z = a * (F + M + E + R) :=
    congrArg (fun w : ℂ => a * w) hraw_local
  have hdistribute :
      a * (F + M + E + R) =
        a * F + a * M + a * E + a * R := by
    calc
      a * (F + M + E + R) = a * ((F + M + E) + R) := rfl
      _ = a * (F + M + E) + a * R := by
        exact mul_add a (F + M + E) R
      _ = (a * (F + M) + a * E) + a * R := by
        exact congrArg (fun w : ℂ => w + a * R) (mul_add a (F + M) E)
      _ = ((a * F + a * M) + a * E) + a * R := by
        exact congrArg
          (fun w : ℂ => (w + a * E) + a * R)
          (mul_add a F M)
      _ = a * F + a * M + a * E + a * R := rfl
  have hF :
      a * F = eulerMaclaurinPoleClearedZetaFinitePart z :=
    (eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw z).symm
  have hM :
      a * M = eulerMaclaurinPoleClearedZetaMainTerm z :=
    (eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw hz_ne_one).symm
  have hE :
      a * E = eulerMaclaurinPoleClearedZetaEndpointTerm z :=
    (eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw z).symm
  have hR :
      a * R = eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    (eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw z).symm
  have hterms :
      a * F + a * M + a * E + a * R =
        eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
    calc
      a * F + a * M + a * E + a * R =
          eulerMaclaurinPoleClearedZetaFinitePart z + a * M + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => w + a * M + a * E + a * R)
          hF
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => eulerMaclaurinPoleClearedZetaFinitePart z + w + a * E + a * R)
          hM
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z + a * R := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z + w + a * R)
          hE
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z +
            eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z +
              eulerMaclaurinPoleClearedZetaEndpointTerm z + w)
          hR
  calc
    poleClearedRiemannZeta z = a * riemannZeta z :=
      hpole
    _ = a * (F + M + E + R) :=
      hmul_raw
    _ = a * F + a * M + a * E + a * R :=
      hdistribute
    _ = eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
      hterms

/-- Subtracting a left summand from a two-term sum leaves the right summand. -/
theorem complex_add_sub_left_cancel
    (S R : ℂ) :
    (S + R) - S = R := by
  calc
    (S + R) - S = S + R + -S := by
      exact sub_eq_add_neg (S + R) S
    _ = S + (R + -S) := by
      exact add_assoc S R (-S)
    _ = S + (-S + R) := by
      exact congrArg (fun x : ℂ => S + x) (add_comm R (-S))
    _ = (S + -S) + R := by
      exact (add_assoc S (-S) R).symm
    _ = 0 + R := by
      exact congrArg (fun x : ℂ => x + R) (add_neg_cancel S)
    _ = R := by
      exact zero_add R

/-- Removable value of the pole-cleared first-order Euler-Maclaurin formula at
`s = 1`.

This is the endpoint cancellation of the raw formula after multiplying by
`s - 1`: the finite, endpoint, and Bernoulli terms vanish and the main term
has value `N^0 = 1`, matching the residue-normalized removable value
`poleClearedRiemannZeta 1 = 1`. -/
theorem eulerMaclaurin_poleCleared_formula_at_one_from_removable_value :
    poleClearedRiemannZeta (1 : ℂ) =
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
  have hpole : poleClearedRiemannZeta (1 : ℂ) = 1 :=
    poleClearedRiemannZeta_one
  have hfinite :
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) = 0 := by
    let S : ℂ :=
      ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ)),
        1 / (((n : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      ((1 : ℂ) - 1) * S = 0 * S := by
        exact congrArg (fun w : ℂ => w * S) (sub_self (1 : ℂ))
      _ = 0 := by
        exact zero_mul S
  have hmain :
      eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) = 1 := by
    let N : ℂ := ((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ)
    calc
      N ^ ((1 : ℂ) - 1) = N ^ (0 : ℂ) := by
        exact congrArg (fun w : ℂ => N ^ w) (sub_self (1 : ℂ))
      _ = 1 := by
        exact Complex.cpow_zero N
  have hendpoint :
      eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) = 0 := by
    let U : ℂ :=
      1 / (((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) =
          ((1 : ℂ) - 1) * eulerMaclaurinZetaEndpointTerm (1 : ℂ) :=
        eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw (1 : ℂ)
      _ = 0 * eulerMaclaurinZetaEndpointTerm (1 : ℂ) := by
        exact congrArg
          (fun w : ℂ => w * eulerMaclaurinZetaEndpointTerm (1 : ℂ))
          (sub_self (1 : ℂ))
      _ = 0 := by
        exact zero_mul (eulerMaclaurinZetaEndpointTerm (1 : ℂ))
  have hremainder :
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) = 0 := by
    let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore (1 : ℂ)
    calc
      -(((1 : ℂ) - 1) * 1) * I = -(0 * 1) * I := by
        exact congrArg (fun w : ℂ => -(w * 1) * I) (sub_self (1 : ℂ))
      _ = -0 * I := by
        exact congrArg (fun w : ℂ => -w * I) (zero_mul (1 : ℂ))
      _ = 0 * I := by
        exact congrArg (fun w : ℂ => w * I) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := by
        exact zero_mul I
  calc
    poleClearedRiemannZeta (1 : ℂ) = 1 :=
      hpole
    _ = 0 + 1 + 0 + 0 := by
      calc
        (1 : ℂ) = 0 + 1 := by
          exact (zero_add (1 : ℂ)).symm
        _ = 0 + 1 + 0 := by
          exact (add_zero (0 + (1 : ℂ))).symm
        _ = 0 + 1 + 0 + 0 := by
          exact (add_zero (0 + (1 : ℂ) + 0)).symm
    _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
      calc
        0 + 1 + 0 + 0 =
            eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + 1 + 0 + 0 := by
          exact congrArg (fun w : ℂ => w + 1 + 0 + 0) hfinite.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + 0 + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + w + 0 + 0)
            hmain.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + w + 0)
            hendpoint.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + w)
            hremainder.symm

/-- First-order Euler-Maclaurin formula for the pole-cleared zeta on
`1 ≤ Re s ≤ 2`, with cutoff `⌊2 + ‖s‖⌋₊` and explicit Bernoulli integral
remainder. -/
theorem eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    [hz_dec : Decidable (z ≠ 1)] :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  exact match hz_dec with
  | Or.inl hz_ne_one =>
      have hraw :
          riemannZeta z =
            eulerMaclaurinZetaFinitePart z +
              eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z :=
        eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
          z hz_one hz_two hz_ne_one
      eulerMaclaurin_poleCleared_formula_of_raw_formula hz_ne_one hraw
  | Or.inr hz_not_ne_one =>
      have hz_eq_one : z = 1 :=
        of_not_not hz_not_ne_one
      Eq.subst
        (motive := fun w : ℂ =>
          poleClearedRiemannZeta w =
            eulerMaclaurinPoleClearedZetaFinitePart w +
              eulerMaclaurinPoleClearedZetaMainTerm w +
              eulerMaclaurinPoleClearedZetaEndpointTerm w +
              eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder w)
        hz_eq_one.symm
        eulerMaclaurin_poleCleared_formula_at_one_from_removable_value

/-- Euler-Maclaurin formula identifies the difference-defined pole-cleared
remainder with the explicit Bernoulli-periodic integral remainder. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    eulerMaclaurinPoleClearedZetaRemainderTerm z =
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  let S : ℂ :=
    eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z
  have hformula :
      poleClearedRiemannZeta z = S + R :=
    eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two
  have hsub :
      poleClearedRiemannZeta z - S = (S + R) - S :=
    congrArg (fun w : ℂ => w - S) hformula
  have hcancel : (S + R) - S = R :=
    complex_add_sub_left_cancel S R
  exact Eq.trans hsub hcancel

/-- The first periodic Bernoulli sawtooth is bounded by one in absolute value. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_abs_le_one
    (x : ℝ) :
    |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 := by
  have hnorm :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ =
        |eulerMaclaurinFirstPeriodicBernoulli x| :=
    RCLike.norm_ofReal (eulerMaclaurinFirstPeriodicBernoulli x)
  have hnorm_le :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hnorm
    hnorm_le

/-- Positive-real complex powers in the Euler-Maclaurin tail are bounded by the
corresponding real power majorant. -/
theorem norm_real_cpow_neg_z_add_one_le_rpow
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ)
    (_hz_one : 1 ≤ z.re) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z + 1)).re := by
    calc
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
          Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
      _ = x ^ (-(z + 1)).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun t : ℝ => -(z.re + t)) Complex.one_re
  exact le_of_eq
    (Eq.trans hnorm (congrArg (fun e : ℝ => x ^ e) hre))

/-- Scalar tail integral bound for the real power majorant after a cutoff
`N ≥ 1` and exponent `σ ≥ 1`. -/
theorem integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
    {N σ : ℝ}
    (hN : 1 ≤ N)
    (hσ : 1 ≤ σ) :
    ∫ x in Set.Ioi N, x ^ (-(σ + 1)) ≤ 1 := by
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN
  have htwo_le : (2 : ℝ) ≤ σ + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ σ + 1 :=
        add_le_add hσ le_rfl
  have hone_lt : (1 : ℝ) < σ + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(σ + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hintegral :
      ∫ x in Set.Ioi N, x ^ (-(σ + 1)) =
        -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) :=
    integral_Ioi_rpow_of_lt ha hN_pos
  have hden : -(σ + 1) + 1 = -σ := by
    calc
      -(σ + 1) + 1 = (-σ + -1) + 1 := by
        exact congrArg (fun t : ℝ => t + 1) (neg_add σ 1)
      _ = -σ + (-1 + 1) := by
        exact add_assoc (-σ) (-1) 1
      _ = -σ + 0 := by
        exact congrArg (fun t : ℝ => -σ + t) (neg_add_cancel (1 : ℝ))
      _ = -σ := by
        exact add_zero (-σ)
  have hvalue :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
        N ^ (-σ) / σ := by
    have hnum :
        N ^ (-(σ + 1) + 1) = N ^ (-σ) :=
      congrArg (fun e : ℝ => N ^ e) hden
    calc
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
          -N ^ (-σ) / (-(σ + 1) + 1) := by
        exact congrArg
          (fun t : ℝ => -t / (-(σ + 1) + 1))
          hnum
      _ = -N ^ (-σ) / (-σ) := by
        exact congrArg
          (fun t : ℝ => -N ^ (-σ) / t)
          hden
      _ = N ^ (-σ) / σ := by
        exact neg_div_neg_eq (N ^ (-σ)) σ
  have hsigma_nonneg : 0 ≤ σ :=
    le_trans zero_le_one hσ
  have hsigma_pos : 0 < σ :=
    lt_of_lt_of_le zero_lt_one hσ
  have hexponent_nonpos : -σ ≤ 0 :=
    neg_nonpos.mpr hsigma_nonneg
  have hpow_le : N ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hexponent_nonpos
  have hquotient_le_one_div :
      N ^ (-σ) / σ ≤ 1 / σ :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hsigma_pos)
  have hone_div_le_one :
      1 / σ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hσ)
      (le_of_eq (div_one (1 : ℝ)))
  have htail :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) ≤ 1 :=
    le_trans
      (Eq.subst
        (motive := fun t : ℝ => t ≤ 1 / σ)
        hvalue.symm
        hquotient_le_one_div)
      hone_div_le_one
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hintegral.symm
    htail

end
end LFunctions
end Boundary
