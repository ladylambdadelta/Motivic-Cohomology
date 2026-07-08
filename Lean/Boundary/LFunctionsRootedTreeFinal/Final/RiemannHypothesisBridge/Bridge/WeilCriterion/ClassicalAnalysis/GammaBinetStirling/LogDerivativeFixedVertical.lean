import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Derivatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.FixedVertical
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm

/-!
# Fixed-vertical Gamma logarithmic-derivative bounds

This file owns fixed-real-part consequences of the Binet logarithmic-derivative
formula.  Value bounds for `Gamma` and `Gamma⁻¹` live in `FixedVertical`; this
file is specifically for the logarithmic derivative `Gamma'/Gamma`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- The fixed-real-part line has positive real part when its real coordinate is
positive. -/
theorem Complex.fixedRealPartLine_re_pos
    {σ t : ℝ}
    (hσ : 0 < σ) :
    0 < (σ + t * Complex.I : ℂ).re := by
  have hre : (σ + t * Complex.I : ℂ).re = σ :=
    Complex.fixedRealPartLine_re σ t
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hre.symm
      hσ

/-- Binet's logarithmic-derivative identity on a fixed positive real-part
vertical line, with the existing principal-log coherence package supplying the
Abel-Plana finite-formula inputs. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    deriv Complex.Gamma (σ + t * Complex.I) /
        Complex.Gamma (σ + t * Complex.I) =
      (Complex.log (σ + t * Complex.I) -
          (1 / (2 * (σ + t * Complex.I)))) +
        2 * ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (-(u : ℂ) /
              ((σ + t * Complex.I) ^ 2 + (u : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * u : ℝ) : ℂ) - 1) := by
  let w : ℂ := σ + t * Complex.I
  have hw_re_pos : 0 < w.re :=
    Complex.fixedRealPartLine_re_pos hσ
  have hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w :=
    (hcoh.2.2 w hw_re_pos).1
  have hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z :=
    (hcoh.2.2 w hw_re_pos).2
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
      hw_re_pos hfinite_w hfinite_nhds

/-- The fixed-real-part Binet main term in the Gamma logarithmic derivative. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalMain
    (σ t : ℝ) : ℂ :=
  Complex.log (σ + t * Complex.I) -
    (1 / (2 * (σ + t * Complex.I)))

/-- The fixed-real-part differentiated Binet remainder in the Gamma
logarithmic derivative. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalRemainder
    (σ t : ℝ) : ℂ :=
  2 * ∫ u : ℝ in Set.Ioi (0 : ℝ),
    (-(u : ℂ) / ((σ + t * Complex.I) ^ 2 + (u : ℂ) ^ 2)) /
      (Complex.exp (((2 : ℝ) * Real.pi * u : ℝ) : ℂ) - 1)

/-- Measurability of a fixed-real-part vertical line. -/
theorem Complex.fixedRealPartLine_measurable
    (σ : ℝ) :
    Measurable (fun t : ℝ => (σ + t * Complex.I : ℂ)) := by
  have ht : Measurable (fun t : ℝ => (t : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_id
  exact measurable_const.add (ht.mul measurable_const)

/-- Strong measurability of the fixed-real-part Binet main term. -/
theorem Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable
    (σ : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => Complex.GammaLogDerivativeFixedVerticalMain σ t)
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ => (σ + t * Complex.I : ℂ)
  have hline : Measurable line :=
    Complex.fixedRealPartLine_measurable σ
  have hlog : Measurable (fun t : ℝ => Complex.log (line t)) :=
    Complex.measurable_log.comp hline
  have hden : Measurable (fun t : ℝ => (2 : ℂ) * line t) :=
    measurable_const.mul hline
  have hhalf : Measurable (fun t : ℝ => (1 : ℂ) / ((2 : ℂ) * line t)) :=
    measurable_const.div hden
  have hmain :
      Measurable
        (fun t : ℝ =>
          Complex.log (line t) - (1 : ℂ) / ((2 : ℂ) * line t)) :=
    hlog.sub hhalf
  exact hmain.aestronglyMeasurable

/-- Joint measurability of the differentiated Binet kernel after restricting
the second variable to a fixed vertical line. -/
theorem Complex.binetSecondFormulaDerivativeKernel_fixedVertical_joint_measurable
    (σ : ℝ) :
    Measurable
      (fun p : ℝ × ℝ =>
        Complex.binetSecondFormulaDerivativeKernel p.2
          (σ + p.1 * Complex.I : ℂ)) := by
  let verticalLine : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ => (σ + p.1 * Complex.I : ℂ)
  let height : ℝ × ℝ → ℂ := fun p : ℝ × ℝ => (p.2 : ℂ)
  have hheight : Measurable height :=
    Complex.measurable_ofReal.comp measurable_snd
  have hline : Measurable verticalLine := by
    have hreal : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
      Complex.measurable_ofReal.comp measurable_fst
    exact measurable_const.add (hreal.mul measurable_const)
  have hnum : Measurable (fun p : ℝ × ℝ => -height p) :=
    hheight.neg
  have hden :
      Measurable
        (fun p : ℝ × ℝ => verticalLine p ^ 2 + height p ^ 2) :=
    (hline.pow_const 2).add (hheight.pow_const 2)
  have hrational :
      Measurable
        (fun p : ℝ × ℝ =>
          -height p / (verticalLine p ^ 2 + height p ^ 2)) :=
    hnum.div hden
  have hexp_den :
      Measurable
        (fun p : ℝ × ℝ =>
          Complex.exp (((2 : ℝ) * Real.pi * p.2 : ℝ) : ℂ) - 1) := by
    have hlinear :
        Measurable
          (fun p : ℝ × ℝ => (((2 : ℝ) * Real.pi * p.2 : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        ((measurable_const.mul measurable_const).mul measurable_snd)
    exact hlinear.cexp.sub measurable_const
  show
    Measurable
      (fun p : ℝ × ℝ =>
        (-(p.2 : ℂ) /
            ((σ + p.1 * Complex.I : ℂ) ^ 2 + (p.2 : ℂ) ^ 2)) /
          (Complex.exp (((2 : ℝ) * Real.pi * p.2 : ℝ) : ℂ) - 1))
  exact hrational.div hexp_den

/-- Strong measurability of the fixed-vertical differentiated Binet remainder
as a function of the vertical parameter. -/
theorem Complex.GammaLogDerivativeFixedVerticalRemainder_aestronglyMeasurable
    (σ : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => Complex.GammaLogDerivativeFixedVerticalRemainder σ t)
      (volume : Measure ℝ) := by
  let μ : Measure ℝ := Measure.restrict volume (Set.Ioi (0 : ℝ))
  let K : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ =>
      Complex.binetSecondFormulaDerivativeKernel p.2
        (σ + p.1 * Complex.I : ℂ)
  have hK :
      AEStronglyMeasurable K ((volume : Measure ℝ).prod μ) :=
    (Complex.binetSecondFormulaDerivativeKernel_fixedVertical_joint_measurable
      σ).aestronglyMeasurable
  have hintegral :
      AEStronglyMeasurable
        (fun t : ℝ => ∫ u : ℝ, K (t, u) ∂μ)
        (volume : Measure ℝ) :=
    hK.integral_prod_right'
  have hscaled :
      AEStronglyMeasurable
        (fun t : ℝ => (2 : ℂ) * ∫ u : ℝ, K (t, u) ∂μ)
        (volume : Measure ℝ) :=
    hintegral.const_mul (2 : ℂ)
  have hfun :
      (fun t : ℝ => Complex.GammaLogDerivativeFixedVerticalRemainder σ t) =
        (fun t : ℝ => (2 : ℂ) * ∫ u : ℝ, K (t, u) ∂μ) := by
    funext t
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hfun.symm
      hscaled

/-- Fixed-line Binet decomposition using named main and remainder pieces. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    deriv Complex.Gamma (σ + t * Complex.I) /
        Complex.Gamma (σ + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalMain σ t +
        Complex.GammaLogDerivativeFixedVerticalRemainder σ t := by
  exact
    Complex.Gamma_logDerivative_fixedRealPartLine_eq_binet hcoh hσ t

/-- Pointwise polynomial bounds for the fixed-line Binet main term and
differentiated remainder imply the same kind of bound for `Gamma'/Gamma`. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_bound_of_main_remainder
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ : 0 < σ)
    (N : ℕ)
    (M R : ℝ)
    (hmain :
      ∀ t : ℝ,
        ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤
          M * (1 + ‖t‖) ^ N)
    (hremainder :
      ∀ t : ℝ,
        ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
          R * (1 + ‖t‖) ^ N) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        (M + R) * (1 + ‖t‖) ^ N := by
  intro t
  let A : ℂ := Complex.GammaLogDerivativeFixedVerticalMain σ t
  let B : ℂ := Complex.GammaLogDerivativeFixedVerticalRemainder σ t
  have hdecomp :
      deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I) =
        A + B :=
    Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
      hcoh hσ t
  have htriangle :
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        ‖A‖ + ‖B‖ := by
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ ‖A‖ + ‖B‖)
        hdecomp.symm
        (norm_add_le A B)
  have hsum :
      ‖A‖ + ‖B‖ ≤
        M * (1 + ‖t‖) ^ N + R * (1 + ‖t‖) ^ N :=
    add_le_add (hmain t) (hremainder t)
  have hfactor :
      M * (1 + ‖t‖) ^ N + R * (1 + ‖t‖) ^ N =
        (M + R) * (1 + ‖t‖) ^ N :=
    (add_mul M R ((1 + ‖t‖) ^ N)).symm
  exact htriangle.trans (hsum.trans_eq hfactor)

/-- The Gamma recurrence in logarithmic-derivative form. -/
theorem Complex.logDeriv_Gamma_add_one
    {s : ℂ}
    (hs0 : s ≠ 0)
    (hs_not_pole : ∀ n : ℕ, s ≠ -n) :
    logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
      logDeriv Complex.Gamma s + 1 / s := by
  have hs_add_not_pole : ∀ n : ℕ, s + 1 ≠ -n := by
    intro n hs_add
    have hcast_nat :
        (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + ((1 : ℕ) : ℂ) :=
      Nat.cast_add n 1
    have hone_nat : (((1 : ℕ) : ℂ)) = (1 : ℂ) :=
      Nat.cast_one
    have hcast : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + (1 : ℂ) :=
      hcast_nat.trans (congrArg (fun x : ℂ => (n : ℂ) + x) hone_nat)
    have hs_neg_succ : s = -(n + 1 : ℕ) := by
      calc
        s = -(n : ℂ) - 1 := by
          exact eq_sub_of_add_eq hs_add
        _ = -((n : ℂ) + 1) := by
          exact (neg_add (n : ℂ) 1).symm
        _ = -((n + 1 : ℕ) : ℂ) := by
          exact congrArg Neg.neg hcast.symm
    exact hs_not_pole (n + 1) hs_neg_succ
  have hGamma_s : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero hs_not_pole
  have hGamma_add : Complex.Gamma (s + 1) ≠ 0 :=
    Complex.Gamma_ne_zero hs_add_not_pole
  have hdiff_s : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s hs_not_pole
  have hdiff_add : DifferentiableAt ℂ Complex.Gamma (s + 1) :=
    Complex.differentiableAt_Gamma (s + 1) hs_add_not_pole
  have hshift_diff :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) s := by
    have htrans : DifferentiableAt ℂ (fun z : ℂ => z + 1) s :=
      DifferentiableAt.add differentiableAt_id
        (differentiableAt_const (1 : ℂ))
    exact hdiff_add.comp s htrans
  have hmul_diff :
      DifferentiableAt ℂ (fun z : ℂ => z * Complex.Gamma z) s :=
    differentiableAt_id.mul hdiff_s
  have hrec :
      (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[𝓝 s]
        (fun z : ℂ => z * Complex.Gamma z) :=
    (eventually_ne_nhds hs0).mono
      (fun z hz => Complex.Gamma_add_one z hz)
  have hlog_shift :
      logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
        logDeriv (fun z : ℂ => z * Complex.Gamma z) s := by
    have hderiv_eq :
        deriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
          deriv (fun z : ℂ => z * Complex.Gamma z) s :=
      hrec.deriv_eq
    have hvalue_eq :
        Complex.Gamma (s + 1) = s * Complex.Gamma s :=
      Complex.Gamma_add_one s hs0
    calc
      logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
          deriv (fun z : ℂ => Complex.Gamma (z + 1)) s /
            Complex.Gamma (s + 1) := by
        exact logDeriv_apply (fun z : ℂ => Complex.Gamma (z + 1)) s
      _ =
          deriv (fun z : ℂ => z * Complex.Gamma z) s /
            (s * Complex.Gamma s) := by
        exact congrArg₂ HDiv.hDiv hderiv_eq hvalue_eq
      _ = logDeriv (fun z : ℂ => z * Complex.Gamma z) s := by
        exact (logDeriv_apply (fun z : ℂ => z * Complex.Gamma z) s).symm
  have hlog_mul :
      logDeriv (fun z : ℂ => z * Complex.Gamma z) s =
        logDeriv (fun z : ℂ => z) s + logDeriv Complex.Gamma s :=
    logDeriv_mul
      (f := fun z : ℂ => z)
      (g := Complex.Gamma)
      s hs0 hGamma_s differentiableAt_id hdiff_s
  have hid :
      logDeriv (fun z : ℂ => z) s = 1 / s :=
    logDeriv_id' s
  calc
    logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
        logDeriv (fun z : ℂ => z * Complex.Gamma z) s :=
      hlog_shift
    _ = logDeriv (fun z : ℂ => z) s + logDeriv Complex.Gamma s :=
      hlog_mul
    _ = 1 / s + logDeriv Complex.Gamma s := by
      exact congrArg (fun z : ℂ => z + logDeriv Complex.Gamma s) hid
    _ = logDeriv Complex.Gamma s + 1 / s :=
      add_comm (1 / s) (logDeriv Complex.Gamma s)

/-- The Gamma recurrence in quotient logarithmic-derivative form. -/
theorem Complex.Gamma_logDerivative_add_one
    {s : ℂ}
    (hs0 : s ≠ 0)
    (hs_not_pole : ∀ n : ℕ, s ≠ -n) :
    deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) =
      deriv Complex.Gamma s / Complex.Gamma s + 1 / s := by
  have hlog :
      logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
        logDeriv Complex.Gamma s + 1 / s :=
    Complex.logDeriv_Gamma_add_one hs0 hs_not_pole
  have hleft_deriv :
      deriv (fun z : ℂ => Complex.Gamma (z + 1)) s =
        deriv Complex.Gamma (s + 1) :=
    deriv_comp_add_const Complex.Gamma (1 : ℂ) s
  calc
    deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) =
        deriv (fun z : ℂ => Complex.Gamma (z + 1)) s /
          Complex.Gamma (s + 1) := by
      exact congrArg (fun z : ℂ => z / Complex.Gamma (s + 1)) hleft_deriv.symm
    _ = logDeriv (fun z : ℂ => Complex.Gamma (z + 1)) s := by
      exact (logDeriv_apply (fun z : ℂ => Complex.Gamma (z + 1)) s).symm
    _ = logDeriv Complex.Gamma s + 1 / s :=
      hlog
    _ = deriv Complex.Gamma s / Complex.Gamma s + 1 / s := by
      exact congrArg (fun z : ℂ => z + 1 / s)
        (logDeriv_apply Complex.Gamma s)

/-- Avoidance of the ordinary Gamma pole locus on a fixed vertical line implies
that the fixed real part is nonzero. -/
theorem Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
    {σ : ℝ}
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    σ ≠ 0 := by
  intro hσ
  have hline_zero :
      (σ + (0 : ℝ) * Complex.I : ℂ) = 0 := by
    calc
      (σ + (0 : ℝ) * Complex.I : ℂ) =
          (σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
        exact Eq.refl _
      _ = (0 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
        exact congrArg (fun x : ℂ => x + ((0 : ℝ) : ℂ) * Complex.I)
          (congrArg (fun x : ℝ => (x : ℂ)) hσ)
      _ = (0 : ℂ) + 0 * Complex.I := by
        exact Eq.refl _
      _ = (0 : ℂ) + 0 := by
        exact congrArg (fun x : ℂ => (0 : ℂ) + x)
          (zero_mul Complex.I)
      _ = 0 := zero_add 0
  have hzero_neg :
      (0 : ℂ) = -(0 : ℕ) := by
    have hcast : (((0 : ℕ) : ℂ)) = (0 : ℂ) :=
      Nat.cast_zero
    have hneg_cast : -(((0 : ℕ) : ℂ)) = -((0 : ℂ)) :=
      congrArg Neg.neg hcast
    exact (hneg_cast.trans (neg_zero : -((0 : ℂ)) = 0)).symm
  exact (hnot_pole 0 0) (hline_zero.trans hzero_neg)

/-- One-step shifted Binet main term for the Gamma logarithmic derivative on a
fixed vertical line.  It is the positive-line main term at real part `σ + 1`,
transported back by the Gamma recurrence. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftOneMain
    (σ t : ℝ) : ℂ :=
  Complex.GammaLogDerivativeFixedVerticalMain (σ + 1) t -
    1 / (σ + t * Complex.I : ℂ)

/-- One-step shifted Binet remainder for the Gamma logarithmic derivative on a
fixed vertical line. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftOneRemainder
    (σ t : ℝ) : ℂ :=
  Complex.GammaLogDerivativeFixedVerticalRemainder (σ + 1) t

/-- One-step shifted fixed-line Binet decomposition for the Gamma logarithmic
derivative.

This extends the positive-real-part Binet decomposition one step to the left
using the Gamma recurrence in logarithmic-derivative form. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftOne_main_add_remainder
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ_shift_pos : 0 < σ + 1)
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n)
    (t : ℝ) :
    deriv Complex.Gamma (σ + t * Complex.I) /
        Complex.Gamma (σ + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalShiftOneMain σ t +
        Complex.GammaLogDerivativeFixedVerticalShiftOneRemainder σ t := by
  let s : ℂ := σ + t * Complex.I
  let shifted : ℂ := ((σ + 1 : ℝ) + t * Complex.I : ℂ)
  have hs0 : s ≠ 0 := by
    have hσ_ne_zero : σ ≠ 0 :=
      Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
        hnot_pole
    intro hs0_eq
    have hre : s.re = (0 : ℂ).re :=
      congrArg Complex.re hs0_eq
    have hs_re : s.re = σ :=
      Complex.fixedRealPartLine_re σ t
    have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
      Complex.zero_re
    exact hσ_ne_zero (hs_re.symm.trans (hre.trans hzero_re))
  have hline_shift : s + 1 = shifted := by
    calc
      s + 1 = ((σ : ℂ) + t * Complex.I) + 1 := by
        exact Eq.refl _
      _ = ((σ : ℂ) + 1) + t * Complex.I := by
        exact add_right_comm (σ : ℂ) (t * Complex.I) 1
      _ = ((σ + 1 : ℝ) : ℂ) + t * Complex.I := by
        have hone : (((1 : ℝ) : ℂ)) = (1 : ℂ) :=
          rfl
        have hreal :
            ((σ : ℂ) + 1) = ((σ + 1 : ℝ) : ℂ) :=
          (congrArg (fun z : ℂ => (σ : ℂ) + z) hone.symm).trans
            (Complex.ofReal_add σ 1).symm
        exact congrArg (fun z : ℂ => z + t * Complex.I)
          hreal
      _ = shifted := by
        exact rfl
  have hshift_decomp :
      deriv Complex.Gamma shifted / Complex.Gamma shifted =
        Complex.GammaLogDerivativeFixedVerticalMain (σ + 1) t +
          Complex.GammaLogDerivativeFixedVerticalRemainder (σ + 1) t := by
    exact
      Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
        hcoh hσ_shift_pos t
  have hrec :
      deriv Complex.Gamma shifted / Complex.Gamma shifted =
        deriv Complex.Gamma s / Complex.Gamma s + 1 / s := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          deriv Complex.Gamma z / Complex.Gamma z =
            deriv Complex.Gamma s / Complex.Gamma s + 1 / s)
        hline_shift
        (Complex.Gamma_logDerivative_add_one
          (s := s) hs0 (hnot_pole t))
  have hsolve :
      deriv Complex.Gamma s / Complex.Gamma s =
        deriv Complex.Gamma shifted / Complex.Gamma shifted - 1 / s :=
    (eq_sub_iff_add_eq).mpr hrec.symm
  calc
    deriv Complex.Gamma s / Complex.Gamma s =
        deriv Complex.Gamma shifted / Complex.Gamma shifted - 1 / s :=
      hsolve
    _ =
        (Complex.GammaLogDerivativeFixedVerticalMain (σ + 1) t +
            Complex.GammaLogDerivativeFixedVerticalRemainder (σ + 1) t) -
          1 / s := by
      exact congrArg (fun z : ℂ => z - 1 / s) hshift_decomp
    _ =
        (Complex.GammaLogDerivativeFixedVerticalMain (σ + 1) t - 1 / s) +
          Complex.GammaLogDerivativeFixedVerticalRemainder (σ + 1) t := by
      let A : ℂ := Complex.GammaLogDerivativeFixedVerticalMain (σ + 1) t
      let B : ℂ := Complex.GammaLogDerivativeFixedVerticalRemainder (σ + 1) t
      let C : ℂ := 1 / s
      calc
        (A + B) - C = (A + B) + -C := by
          exact sub_eq_add_neg (A + B) C
        _ = A + (B + -C) := by
          exact add_assoc A B (-C)
        _ = A + (-C + B) := by
          exact congrArg (fun z : ℂ => A + z) (add_comm B (-C))
        _ = (A + -C) + B := by
          exact (add_assoc A (-C) B).symm
        _ = (A - C) + B := by
          exact congrArg (fun z : ℂ => z + B)
            (sub_eq_add_neg A C).symm
    _ =
        Complex.GammaLogDerivativeFixedVerticalShiftOneMain σ t +
          Complex.GammaLogDerivativeFixedVerticalShiftOneRemainder σ t := by
      exact Eq.refl _

/-- Ordinary Gamma pole avoidance on a fixed vertical line is stable under
shifting the fixed real part to the right by a natural number. -/
theorem Complex.fixedRealPartLine_shift_nat_ne_Gamma_zero_locus
    {σ : ℝ}
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n)
    (k : ℕ) :
    ∀ t : ℝ, ∀ n : ℕ,
      (σ + (k : ℝ) + t * Complex.I : ℂ) ≠ -n := by
  intro t n hshift
  have hsubtract :
      (σ + t * Complex.I : ℂ) =
        (σ + (k : ℝ) + t * Complex.I : ℂ) - (k : ℂ) := by
    calc
      (σ + t * Complex.I : ℂ) =
          ((σ : ℂ) + t * Complex.I) := by
        exact Eq.refl _
      _ = (((σ : ℂ) + t * Complex.I) + (k : ℂ)) - (k : ℂ) := by
        exact
          (add_sub_cancel_right
            ((σ : ℂ) + t * Complex.I)
            (k : ℂ)).symm
      _ = (((σ : ℂ) + (k : ℂ)) + t * Complex.I) - (k : ℂ) := by
        exact
          congrArg (fun z : ℂ => z - (k : ℂ))
            (add_right_comm (σ : ℂ) (t * Complex.I) (k : ℂ))
      _ = (σ + (k : ℝ) + t * Complex.I : ℂ) - (k : ℂ) := by
        have hk : (((k : ℝ) : ℂ)) = (k : ℂ) :=
          rfl
        have hreal :
            ((σ : ℂ) + (k : ℂ)) = (σ : ℂ) + ((k : ℝ) : ℂ) :=
          congrArg (fun z : ℂ => (σ : ℂ) + z) hk.symm
        exact congrArg (fun z : ℂ => z - (k : ℂ))
          (congrArg (fun z : ℂ => z + t * Complex.I)
            hreal)
  have hneg_sub :
      (-(n : ℂ)) - (k : ℂ) = -((n + k : ℕ) : ℂ) := by
    have hcast :
        (((n + k : ℕ) : ℂ)) = (n : ℂ) + (k : ℂ) :=
      Nat.cast_add n k
    calc
      (-(n : ℂ)) - (k : ℂ) =
          -(n : ℂ) + -(k : ℂ) := by
        exact sub_eq_add_neg (-(n : ℂ)) (k : ℂ)
      _ = -((n : ℂ) + (k : ℂ)) := by
        exact (neg_add (n : ℂ) (k : ℂ)).symm
      _ = -((n + k : ℕ) : ℂ) := by
        exact congrArg Neg.neg hcast.symm
  have horiginal :
      (σ + t * Complex.I : ℂ) = -((n + k : ℕ) : ℂ) := by
    calc
      (σ + t * Complex.I : ℂ) =
          (σ + (k : ℝ) + t * Complex.I : ℂ) - (k : ℂ) :=
        hsubtract
      _ = (-(n : ℂ)) - (k : ℂ) := by
        exact congrArg (fun z : ℂ => z - (k : ℂ)) hshift
      _ = -((n + k : ℕ) : ℂ) :=
        hneg_sub
  exact (hnot_pole t (n + k)) horiginal

/-- The explicit fixed-positive-line constant for the Gamma logarithmic
derivative bound. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant
    (σ : ℝ) : ℝ :=
  (((|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ) +
    |‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / σ ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|)

/-- The finite right-shift constant obtained by iterating the Gamma recurrence
until the fixed real part lies in the positive half-plane. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftConstant
    (σ : ℝ) : ℕ → ℝ
  | 0 => Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant σ
  | Nat.succ N =>
      Complex.GammaLogDerivativeFixedVerticalShiftConstant (σ + 1) N +
        |σ|⁻¹

/-- Adding one and then a natural shift is the same real coordinate as shifting
by the successor. -/
theorem Complex.real_add_one_add_nat_eq_add_succ
    (σ : ℝ) (N : ℕ) :
    σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) := by
  have hcast_nat :
      (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + ((1 : ℕ) : ℝ) :=
    Nat.cast_add N 1
  have hone_nat : (((1 : ℕ) : ℝ)) = (1 : ℝ) :=
    Nat.cast_one
  have hcast :
      (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + (1 : ℝ) :=
    hcast_nat.trans (congrArg (fun x : ℝ => (N : ℝ) + x) hone_nat)
  calc
    σ + ((N + 1 : ℕ) : ℝ) =
        σ + ((N : ℝ) + 1) := by
      exact congrArg (fun x : ℝ => σ + x) hcast
    _ = (σ + (N : ℝ)) + 1 := by
      exact (add_assoc σ (N : ℝ) 1).symm
    _ = (σ + 1) + (N : ℝ) := by
      exact add_right_comm σ (N : ℝ) 1

/-- One-step pole avoidance on a fixed vertical line, in the canonical
`(σ + 1 : ℝ)` real-part normal form. -/
theorem Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus
    {σ : ℝ}
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ, ∀ n : ℕ,
      ((σ + 1 : ℝ) + t * Complex.I : ℂ) ≠ -n := by
  intro t n hshift
  have hraw :
      (σ + (1 : ℝ) + t * Complex.I : ℂ) ≠ -n :=
    have hraw_nat :
        (σ + ((1 : ℕ) : ℝ) + t * Complex.I : ℂ) ≠ -n :=
      Complex.fixedRealPartLine_shift_nat_ne_Gamma_zero_locus
        hnot_pole 1 t n
    have hone_nat : (((1 : ℕ) : ℝ)) = (1 : ℝ) :=
      Nat.cast_one
    have hline_nat :
        (σ + ((1 : ℕ) : ℝ) + t * Complex.I : ℂ) =
          (σ + (1 : ℝ) + t * Complex.I : ℂ) := by
      exact congrArg (fun x : ℝ => (σ + x + t * Complex.I : ℂ))
        hone_nat
    fun h => hraw_nat (hline_nat.trans h)
  have hline :
      (σ + (1 : ℝ) + t * Complex.I : ℂ) =
        ((σ + 1 : ℝ) + t * Complex.I : ℂ) := by
    exact congrArg (fun z : ℂ => z + t * Complex.I)
      (Complex.ofReal_add σ 1).symm
  exact hraw (hline.trans hshift)

/-- Finite-shift Binet main term for the Gamma logarithmic derivative on a
fixed vertical line.

At shift `0` this is the usual positive-line Binet main term.  At a successor
shift, the Gamma recurrence transports the shifted main term one step left and
adds the reciprocal correction with the recurrence sign. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftNatMain
    (σ : ℝ) : ℕ → ℝ → ℂ
  | 0, t => Complex.GammaLogDerivativeFixedVerticalMain σ t
  | Nat.succ N, t =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain (σ + 1) N t -
        1 / (σ + t * Complex.I : ℂ)

/-- Finite-shift Binet remainder for the Gamma logarithmic derivative on a
fixed vertical line.  The recurrence contributes only to the main term, so the
remainder is transported unchanged from the shifted positive line. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
    (σ : ℝ) : ℕ → ℝ → ℂ
  | 0, t => Complex.GammaLogDerivativeFixedVerticalRemainder σ t
  | Nat.succ N, t =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder (σ + 1) N t

/-- Strong measurability of the finite-shift Binet main term. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatMain_aestronglyMeasurable
    (σ : ℝ) :
    ∀ N : ℕ,
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N t)
        (volume : Measure ℝ) := by
  intro N
  induction N generalizing σ with
  | zero =>
      exact Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable σ
  | succ N ih =>
      let line : ℝ → ℂ := fun t : ℝ => (σ + t * Complex.I : ℂ)
      have htail :
          AEStronglyMeasurable
            (fun t : ℝ =>
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                (σ + 1) N t)
            (volume : Measure ℝ) :=
        ih (σ + 1)
      have hline : Measurable line :=
        Complex.fixedRealPartLine_measurable σ
      have hinv :
          AEStronglyMeasurable
            (fun t : ℝ => (1 : ℂ) / line t)
          (volume : Measure ℝ) :=
        (measurable_const.div hline).aestronglyMeasurable
      exact htail.sub hinv

/-- Strong measurability of the finite-shift Binet remainder. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_aestronglyMeasurable
    (σ : ℝ) :
    ∀ N : ℕ,
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N t)
        (volume : Measure ℝ) := by
  intro N
  induction N generalizing σ with
  | zero =>
      exact Complex.GammaLogDerivativeFixedVerticalRemainder_aestronglyMeasurable σ
  | succ N ih =>
      exact ih (σ + 1)

/-- Finite shifted fixed-line Binet decomposition for the Gamma logarithmic
derivative.

If a natural right-shift of the fixed real part lies in the positive
half-plane and the original fixed line avoids the ordinary Gamma pole locus,
then the Binet decomposition transports back to the original line by iterating
the Gamma recurrence. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftNat_main_add_remainder
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (N : ℕ)
    (hσ_shift_pos : 0 < σ + (N : ℝ))
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n)
    (t : ℝ) :
    deriv Complex.Gamma (σ + t * Complex.I) /
        Complex.Gamma (σ + t * Complex.I) =
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N t +
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N t := by
  induction N generalizing σ with
  | zero =>
      have hσ_pos : 0 < σ := by
        have hzero : σ + ((0 : ℕ) : ℝ) = σ := by
          have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
            Nat.cast_zero
          exact (congrArg (fun x : ℝ => σ + x) hcast).trans (add_zero σ)
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hzero
            hσ_shift_pos
      calc
        deriv Complex.Gamma (σ + t * Complex.I) /
            Complex.Gamma (σ + t * Complex.I) =
          Complex.GammaLogDerivativeFixedVerticalMain σ t +
            Complex.GammaLogDerivativeFixedVerticalRemainder σ t :=
          Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
            hcoh hσ_pos t
        _ =
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ 0 t +
            Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ 0 t := by
          exact Eq.refl _
  | succ N ih =>
      let s : ℂ := σ + t * Complex.I
      let shifted : ℂ := ((σ + 1 : ℝ) + t * Complex.I : ℂ)
      have htail_pos : 0 < (σ + 1) + (N : ℝ) := by
        have hrewrite :
            σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) :=
          Complex.real_add_one_add_nat_eq_add_succ σ N
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hrewrite
            hσ_shift_pos
      have htail_pole :
          ∀ t : ℝ, ∀ n : ℕ,
            ((σ + 1 : ℝ) + t * Complex.I : ℂ) ≠ -n :=
        Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus
          hnot_pole
      have hs0 : s ≠ 0 := by
        have hσ_ne_zero : σ ≠ 0 :=
          Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
            hnot_pole
        intro hs0_eq
        have hre : s.re = (0 : ℂ).re :=
          congrArg Complex.re hs0_eq
        have hs_re : s.re = σ :=
          Complex.fixedRealPartLine_re σ t
        have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
          Complex.zero_re
        exact hσ_ne_zero (hs_re.symm.trans (hre.trans hzero_re))
      have hline_shift : s + 1 = shifted := by
        calc
          s + 1 = ((σ : ℂ) + t * Complex.I) + 1 := by
            exact Eq.refl _
          _ = ((σ : ℂ) + 1) + t * Complex.I := by
            exact add_right_comm (σ : ℂ) (t * Complex.I) 1
          _ = ((σ + 1 : ℝ) : ℂ) + t * Complex.I := by
            have hone : (((1 : ℝ) : ℂ)) = (1 : ℂ) :=
              rfl
            have hreal :
                ((σ : ℂ) + 1) = ((σ + 1 : ℝ) : ℂ) :=
              (congrArg (fun z : ℂ => (σ : ℂ) + z) hone.symm).trans
                (Complex.ofReal_add σ 1).symm
            exact congrArg (fun z : ℂ => z + t * Complex.I)
              hreal
          _ = shifted := by
            exact rfl
      have hshift_decomp :
          deriv Complex.Gamma shifted / Complex.Gamma shifted =
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              (σ + 1) N t +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
                (σ + 1) N t := by
        exact ih htail_pos htail_pole
      have hrec :
          deriv Complex.Gamma shifted / Complex.Gamma shifted =
            deriv Complex.Gamma s / Complex.Gamma s + 1 / s := by
        exact
          Eq.subst
            (motive := fun z : ℂ =>
              deriv Complex.Gamma z / Complex.Gamma z =
                deriv Complex.Gamma s / Complex.Gamma s + 1 / s)
            hline_shift
            (Complex.Gamma_logDerivative_add_one
              (s := s) hs0 (hnot_pole t))
      have hsolve :
          deriv Complex.Gamma s / Complex.Gamma s =
            deriv Complex.Gamma shifted / Complex.Gamma shifted - 1 / s :=
        (eq_sub_iff_add_eq).mpr hrec.symm
      calc
        deriv Complex.Gamma s / Complex.Gamma s =
            deriv Complex.Gamma shifted / Complex.Gamma shifted - 1 / s :=
          hsolve
        _ =
            (Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                (σ + 1) N t +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
                (σ + 1) N t) -
              1 / s := by
          exact congrArg (fun z : ℂ => z - 1 / s) hshift_decomp
        _ =
            (Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                (σ + 1) N t - 1 / s) +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
                (σ + 1) N t := by
          let A : ℂ :=
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              (σ + 1) N t
          let B : ℂ :=
            Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
              (σ + 1) N t
          let C : ℂ := 1 / s
          calc
            (A + B) - C = (A + B) + -C := by
              exact sub_eq_add_neg (A + B) C
            _ = A + (B + -C) := by
              exact add_assoc A B (-C)
            _ = A + (-C + B) := by
              exact congrArg (fun z : ℂ => A + z) (add_comm B (-C))
            _ = (A + -C) + B := by
              exact (add_assoc A (-C) B).symm
            _ = (A - C) + B := by
              exact congrArg (fun z : ℂ => z + B)
                (sub_eq_add_neg A C).symm
        _ =
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                σ (N + 1) t +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
                σ (N + 1) t := by
          exact Eq.refl _

/-- Every fixed real part admits a natural right-shift into the positive
half-plane. -/
theorem Complex.exists_fixedRealPartLine_positive_shift_nat
    (σ : ℝ) :
    ∃ N : ℕ, 0 < σ + (N : ℝ) := by
  match exists_nat_gt (-σ) with
  | ⟨N, hN⟩ =>
      have hpos : 0 < σ + (N : ℝ) := by
        calc
          0 = σ + -σ := by
            exact (add_neg_cancel σ).symm
          _ < σ + (N : ℝ) := by
            exact add_lt_add_left hN σ
      exact ⟨N, hpos⟩

/-- A canonical finite shift that moves the fixed real part into the positive
half-plane.  The value is chosen only from the archimedean property above; no
contour-family upper bound is required. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat
    (σ : ℝ) : ℕ :=
  Classical.choose (Complex.exists_fixedRealPartLine_positive_shift_nat σ)

/-- The canonical finite shift has positive shifted real part. -/
theorem Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos
    (σ : ℝ) :
    0 <
      σ +
        (Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat σ : ℝ) :=
  Classical.choose_spec
    (Complex.exists_fixedRealPartLine_positive_shift_nat σ)

/-- The differentiated Binet remainder is uniformly bounded on any vertical
region bounded away from the imaginary axis. -/
theorem Complex.binetSecondFormulaRemainderDerivative_norm_le_of_re_ge
    {δ : ℝ}
    (hδ : 0 < δ)
    {w : ℂ}
    (hδ_le_re : δ ≤ w.re) :
    ‖Complex.binetSecondFormulaRemainderDerivative w‖ ≤
      ‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / δ ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)) := by
  let K : ℝ → ℂ :=
    fun u : ℝ => Complex.binetSecondFormulaDerivativeKernel u w
  let M : ℝ → ℝ :=
    fun u : ℝ =>
      (1 / δ ^ 2) *
        (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))
  have hM_integrable :
      Integrable M (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn.const_mul
      (1 / δ ^ 2)
  have hpoint :
      ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖K u‖ ≤ M u :=
    (ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))).mono
      (fun u hu =>
        Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
          hδ hδ_le_re hu)
  have hintegral :
      ‖∫ u : ℝ in Set.Ioi (0 : ℝ), K u‖ ≤
        ∫ u : ℝ in Set.Ioi (0 : ℝ), M u :=
    norm_integral_le_of_norm_le hM_integrable hpoint
  have hdef :
      Complex.binetSecondFormulaRemainderDerivative w =
        (2 : ℂ) * ∫ u : ℝ in Set.Ioi (0 : ℝ), K u :=
    rfl
  have hnorm :
      ‖Complex.binetSecondFormulaRemainderDerivative w‖ =
        ‖(2 : ℂ)‖ * ‖∫ u : ℝ in Set.Ioi (0 : ℝ), K u‖ := by
    calc
      ‖Complex.binetSecondFormulaRemainderDerivative w‖ =
          ‖(2 : ℂ) * ∫ u : ℝ in Set.Ioi (0 : ℝ), K u‖ := by
        exact congrArg norm hdef
      _ = ‖(2 : ℂ)‖ * ‖∫ u : ℝ in Set.Ioi (0 : ℝ), K u‖ :=
        norm_mul (2 : ℂ) (∫ u : ℝ in Set.Ioi (0 : ℝ), K u)
  calc
    ‖Complex.binetSecondFormulaRemainderDerivative w‖ =
        ‖(2 : ℂ)‖ * ‖∫ u : ℝ in Set.Ioi (0 : ℝ), K u‖ :=
      hnorm
    _ ≤ ‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ), M u :=
      mul_le_mul_of_nonneg_left hintegral (norm_nonneg (2 : ℂ))

/-- Fixed-positive-real-part version of the differentiated Binet remainder
bound. -/
theorem Complex.GammaLogDerivativeFixedVerticalRemainder_norm_le_const
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
      ‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / σ ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)) := by
  let w : ℂ := σ + t * Complex.I
  have hδ_le_re : σ ≤ w.re := by
    have hre : w.re = σ :=
      Complex.fixedRealPartLine_re σ t
    exact
      Eq.subst
        (motive := fun x : ℝ => σ ≤ x)
        hre.symm
        (le_refl σ)
  exact
    Complex.binetSecondFormulaRemainderDerivative_norm_le_of_re_ge
      hσ hδ_le_re

/-- The fixed-positive-real-part differentiated Binet remainder has degree-zero
polynomial growth on the vertical line. -/
theorem Complex.GammaLogDerivativeFixedVerticalRemainder_polynomial_bound
    {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ t : ℝ,
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
        (‖(2 : ℂ)‖ *
          ∫ u : ℝ in Set.Ioi (0 : ℝ),
            (1 / σ ^ 2) *
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))) *
          (1 + ‖t‖) ^ (0 : ℕ) := by
  intro t
  let C : ℝ :=
    ‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / σ ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))
  have hconst :
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤ C :=
    Complex.GammaLogDerivativeFixedVerticalRemainder_norm_le_const hσ t
  have hpow :
      (1 + ‖t‖) ^ (0 : ℕ) = (1 : ℝ) :=
    pow_zero (1 + ‖t‖)
  calc
    ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤ C :=
      hconst
    _ = C * (1 + ‖t‖) ^ (0 : ℕ) := by
      calc
        C = C * 1 := by
          exact (mul_one C).symm
        _ = C * (1 + ‖t‖) ^ (0 : ℕ) := by
          exact congrArg (fun x : ℝ => C * x) hpow.symm

/-- A real logarithm with a positive fixed lower bound and linear upper bound
has linear growth. -/
theorem Real.abs_log_le_fixedLower_linearUpper
    {σ A x a : ℝ}
    (hσ : 0 < σ)
    (hA_nonneg : 0 ≤ A)
    (ha_one : 1 ≤ a)
    (hσx : σ ≤ x)
    (hxA : x ≤ A * a) :
    |Real.log x| ≤ (|Real.log σ| + A) * a := by
  let C : ℝ := |Real.log σ| + A
  have hx_pos : 0 < x :=
    lt_of_lt_of_le hσ hσx
  have hlog_lower : Real.log σ ≤ Real.log x :=
    Real.log_le_log hσ hσx
  have hlog_upper : Real.log x ≤ x :=
    Real.log_le_self hx_pos.le
  have hC_nonneg : 0 ≤ C :=
    add_nonneg (abs_nonneg (Real.log σ)) hA_nonneg
  have habs_le_C : |Real.log σ| ≤ C := by
    calc
      |Real.log σ| = |Real.log σ| + 0 := by
        exact (add_zero |Real.log σ|).symm
      _ ≤ |Real.log σ| + A :=
        add_le_add_left hA_nonneg |Real.log σ|
  have hC_le_Ca : C ≤ C * a := by
    calc
      C = C * 1 := by
        exact (mul_one C).symm
      _ ≤ C * a :=
        mul_le_mul_of_nonneg_left ha_one hC_nonneg
  have habs_le_Ca : |Real.log σ| ≤ C * a :=
    habs_le_C.trans hC_le_Ca
  have hleft : -((|Real.log σ| + A) * a) ≤ Real.log x := by
    have hneg_abs : -|Real.log σ| ≤ Real.log σ :=
      neg_abs_le (Real.log σ)
    exact
      le_trans (neg_le_neg habs_le_Ca)
        (le_trans hneg_abs hlog_lower)
  have hright : Real.log x ≤ (|Real.log σ| + A) * a := by
    exact hlog_upper.trans
      (hxA.trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (abs_nonneg (Real.log σ)))
          (zero_le_one.trans ha_one)))
  exact abs_le.mpr ⟨hleft, hright⟩

/-- The norm on a positive fixed-real-part vertical line is bounded below by
the fixed real part. -/
theorem Complex.fixedRealPartLine_norm_lower
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    σ ≤ ‖(σ + t * Complex.I : ℂ)‖ := by
  let z : ℂ := σ + t * Complex.I
  have hre : z.re = σ :=
    Complex.fixedRealPartLine_re σ t
  have hre_abs_le : |z.re| ≤ ‖z‖ :=
    RCLike.abs_re_le_norm z
  have hσ_abs : |σ| = σ :=
    abs_of_nonneg hσ.le
  calc
    σ = |σ| := hσ_abs.symm
    _ = |z.re| := congrArg abs hre.symm
    _ ≤ ‖z‖ := hre_abs_le

/-- The norm on a fixed-real-part vertical line is bounded below by the
absolute value of the fixed real part. -/
theorem Complex.fixedRealPartLine_norm_lower_abs
    {σ : ℝ}
    (t : ℝ) :
    |σ| ≤ ‖(σ + t * Complex.I : ℂ)‖ := by
  let z : ℂ := σ + t * Complex.I
  have hre : z.re = σ :=
    Complex.fixedRealPartLine_re σ t
  have hre_abs_le : |z.re| ≤ ‖z‖ :=
    RCLike.abs_re_le_norm z
  calc
    |σ| = |z.re| := congrArg abs hre.symm
    _ ≤ ‖z‖ := hre_abs_le

/-- The reciprocal of a fixed-real-part vertical line is uniformly bounded
when the fixed real part is nonzero. -/
theorem Complex.fixedRealPartLine_inv_norm_le_abs_re_inv
    {σ : ℝ}
    (hσ : σ ≠ 0)
    (t : ℝ) :
    ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤ |σ|⁻¹ := by
  let z : ℂ := σ + t * Complex.I
  have hσ_abs_pos : 0 < |σ| :=
    abs_pos.mpr hσ
  have hz_lower : |σ| ≤ ‖z‖ :=
    Complex.fixedRealPartLine_norm_lower_abs t
  have hz_norm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le hσ_abs_pos hz_lower
  have hnorm_inv : ‖z⁻¹‖ = (‖z‖)⁻¹ :=
    norm_inv z
  have hinv_le : (‖z‖)⁻¹ ≤ |σ|⁻¹ :=
    inv_le_inv_of_le hσ_abs_pos hz_lower
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ |σ|⁻¹)
      hnorm_inv.symm
      hinv_le

/-- The reciprocal of a nonzero fixed-real-part vertical line has linear
growth bound with exponent zero, expressed in the same majorant shape used by
vertical-channel estimates. -/
theorem Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
    {σ : ℝ}
    (hσ : σ ≠ 0)
    (t : ℝ) :
    ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤ |σ|⁻¹ * (1 + ‖t‖) := by
  have hconst :
      ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤ |σ|⁻¹ :=
    Complex.fixedRealPartLine_inv_norm_le_abs_re_inv hσ t
  have hcoeff_nonneg : 0 ≤ |σ|⁻¹ :=
    inv_nonneg.mpr (abs_nonneg σ)
  have hlinear :
      |σ|⁻¹ ≤ |σ|⁻¹ * (1 + ‖t‖) := by
    calc
      |σ|⁻¹ = |σ|⁻¹ * 1 := by
        exact (mul_one |σ|⁻¹).symm
      _ ≤ |σ|⁻¹ * (1 + ‖t‖) := by
        exact mul_le_mul_of_nonneg_left
          (Real.one_le_one_add_norm t)
          hcoeff_nonneg
  exact hconst.trans hlinear

/-- The norm on a fixed-real-part vertical line is bounded above by the sum of
the real part and the height. -/
theorem Complex.fixedRealPartLine_norm_upper
    {σ : ℝ}
    (hσ : 0 ≤ σ)
    (t : ℝ) :
    ‖(σ + t * Complex.I : ℂ)‖ ≤ σ + ‖t‖ := by
  let X : ℂ := (σ : ℂ)
  let Y : ℂ := (t : ℂ) * Complex.I
  have htriangle : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
    norm_add_le X Y
  have hX : ‖X‖ = σ := by
    calc
      ‖X‖ = |σ| := RCLike.norm_ofReal σ
      _ = σ := abs_of_nonneg hσ
  have hY : ‖Y‖ = ‖t‖ := by
    calc
      ‖Y‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
        norm_mul (t : ℂ) Complex.I
      _ = ‖(t : ℂ)‖ * 1 :=
        congrArg (fun x : ℝ => ‖(t : ℂ)‖ * x) Complex.norm_I
      _ = ‖(t : ℂ)‖ := mul_one ‖(t : ℂ)‖
      _ = ‖t‖ := RCLike.norm_ofReal t
  calc
    ‖(σ + t * Complex.I : ℂ)‖ = ‖X + Y‖ := rfl
    _ ≤ ‖X‖ + ‖Y‖ := htriangle
    _ = σ + ‖t‖ :=
      congrArg₂ HAdd.hAdd hX hY

/-- The principal logarithm on a positive fixed-real-part vertical line has
linear growth in the height. -/
theorem Complex.fixedRealPartLine_log_norm_le_linear
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    ‖Complex.log (σ + t * Complex.I)‖ ≤
      (|Real.log σ| + (σ + 1) + Real.pi) * (1 + ‖t‖) := by
  let z : ℂ := σ + t * Complex.I
  let A : ℝ := σ + 1
  let a : ℝ := 1 + ‖t‖
  have hA_nonneg : 0 ≤ A :=
    add_nonneg hσ.le zero_le_one
  have ha_one : 1 ≤ a :=
    Real.one_le_one_add_norm t
  have hnorm_lower : σ ≤ ‖z‖ :=
    Complex.fixedRealPartLine_norm_lower hσ t
  have hnorm_upper_raw : ‖z‖ ≤ σ + ‖t‖ :=
    Complex.fixedRealPartLine_norm_upper hσ.le t
  have hupper_scalar : σ + ‖t‖ ≤ A * a := by
    have hσ_le_A : σ ≤ A := by
      calc
        σ = σ + 0 := by
          exact (add_zero σ).symm
        _ ≤ σ + 1 :=
          add_le_add_left zero_le_one σ
    have ht_le_a : ‖t‖ ≤ a := by
      calc
        ‖t‖ = 0 + ‖t‖ := by
          exact (zero_add ‖t‖).symm
        _ ≤ 1 + ‖t‖ :=
          add_le_add_right zero_le_one ‖t‖
    have hprod_expand :
        A * a = A * 1 + A * ‖t‖ := by
      calc
        A * a = A * (1 + ‖t‖) := rfl
        _ = A * 1 + A * ‖t‖ :=
          mul_add A 1 ‖t‖
    have hleft : σ ≤ A * 1 := by
      calc
        σ ≤ A := hσ_le_A
        _ = A * 1 := (mul_one A).symm
    have hright : ‖t‖ ≤ A * ‖t‖ := by
      have hone_le_A : 1 ≤ A := by
        calc
          1 = 0 + 1 := by
            exact (zero_add 1).symm
          _ ≤ σ + 1 :=
            add_le_add_right hσ.le 1
      calc
        ‖t‖ = 1 * ‖t‖ := by
          exact (one_mul ‖t‖).symm
        _ ≤ A * ‖t‖ :=
          mul_le_mul_of_nonneg_right hone_le_A (norm_nonneg t)
    calc
      σ + ‖t‖ ≤ A * 1 + A * ‖t‖ :=
        add_le_add hleft hright
      _ = A * a := hprod_expand.symm
  have hlog_abs :
      |Real.log ‖z‖| ≤ (|Real.log σ| + A) * a :=
    Real.abs_log_le_fixedLower_linearUpper
      hσ hA_nonneg ha_one hnorm_lower (hnorm_upper_raw.trans hupper_scalar)
  have hlog :
      ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
    Complex.log_norm_le_abs_log_norm_add_pi z
  have hpi_nonneg : 0 ≤ Real.pi :=
    Real.pi_pos.le
  have hpi_linear : Real.pi ≤ Real.pi * a := by
    calc
      Real.pi = Real.pi * 1 := by
        exact (mul_one Real.pi).symm
      _ ≤ Real.pi * a :=
        mul_le_mul_of_nonneg_left ha_one hpi_nonneg
  have hsum :
      |Real.log ‖z‖| + Real.pi ≤
        (|Real.log σ| + A) * a + Real.pi * a :=
    add_le_add hlog_abs hpi_linear
  have hfactor :
      (|Real.log σ| + A) * a + Real.pi * a =
        (|Real.log σ| + A + Real.pi) * a :=
    (add_mul (|Real.log σ| + A) Real.pi a).symm
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
      hlog
    _ ≤ (|Real.log σ| + A) * a + Real.pi * a :=
      hsum
    _ = (|Real.log σ| + A + Real.pi) * a :=
      hfactor

/-- The inverse part of the Binet main term is uniformly bounded on a positive
fixed-real-part vertical line. -/
theorem Complex.fixedRealPartLine_inv_two_mul_norm_le_const
    {σ : ℝ}
    (hσ : 0 < σ)
    (t : ℝ) :
    ‖(1 : ℂ) / (2 * (σ + t * Complex.I))‖ ≤ 1 / σ := by
  let z : ℂ := σ + t * Complex.I
  have hz_lower : σ ≤ ‖z‖ :=
    Complex.fixedRealPartLine_norm_lower hσ t
  have hden_norm :
      ‖(2 : ℂ) * z‖ = ‖(2 : ℂ)‖ * ‖z‖ :=
    norm_mul (2 : ℂ) z
  have hone_le_two_norm : 1 ≤ ‖(2 : ℂ)‖ := by
    have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
      calc
        ‖(2 : ℂ)‖ = |(2 : ℝ)| := RCLike.norm_ofReal (2 : ℝ)
        _ = (2 : ℝ) := abs_of_nonneg zero_le_two
    exact
      Eq.subst
        (motive := fun x : ℝ => 1 ≤ x)
        htwo_norm.symm
        one_le_two
  have hσ_le_den :
      σ ≤ ‖(2 : ℂ) * z‖ := by
    calc
      σ ≤ ‖z‖ := hz_lower
      _ = 1 * ‖z‖ := (one_mul ‖z‖).symm
      _ ≤ ‖(2 : ℂ)‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_right hone_le_two_norm (norm_nonneg z)
      _ = ‖(2 : ℂ) * z‖ := hden_norm.symm
  have hinv_mono :
      (‖(2 : ℂ) * z‖)⁻¹ ≤ σ⁻¹ :=
    inv_le_inv_of_le hσ hσ_le_den
  have hnorm_eq :
      ‖(1 : ℂ) / (2 * z)‖ = (‖(2 : ℂ) * z‖)⁻¹ := by
    calc
      ‖(1 : ℂ) / (2 * z)‖ =
          ‖(1 : ℂ)‖ / ‖(2 : ℂ) * z‖ :=
        norm_div (1 : ℂ) ((2 : ℂ) * z)
      _ = 1 / ‖(2 : ℂ) * z‖ := by
        exact congrArg (fun x : ℝ => x / ‖(2 : ℂ) * z‖) (norm_one : ‖(1 : ℂ)‖ = 1)
      _ = (‖(2 : ℂ) * z‖)⁻¹ :=
        one_div ‖(2 : ℂ) * z‖
  calc
    ‖(1 : ℂ) / (2 * z)‖ = (‖(2 : ℂ) * z‖)⁻¹ :=
      hnorm_eq
    _ ≤ σ⁻¹ := hinv_mono
    _ = 1 / σ := (one_div σ).symm

/-- The Binet main term for `Gamma'/Gamma` has linear growth on each positive
fixed-real-part vertical line. -/
theorem Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound
    {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ t : ℝ,
      ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤
        ((|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ) *
          (1 + ‖t‖) := by
  intro t
  let L : ℂ := Complex.log (σ + t * Complex.I)
  let I : ℂ := (1 : ℂ) / (2 * (σ + t * Complex.I))
  let A : ℝ := |Real.log σ| + (σ + 1) + Real.pi
  let B : ℝ := 1 / σ
  have hmain_eq :
      Complex.GammaLogDerivativeFixedVerticalMain σ t = L - I :=
    rfl
  have htriangle :
      ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤ ‖L‖ + ‖I‖ := by
    have hsub : ‖L - I‖ ≤ ‖L‖ + ‖I‖ :=
      norm_sub_le L I
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ ‖L‖ + ‖I‖)
        hmain_eq.symm
        hsub
  have hL : ‖L‖ ≤ A * (1 + ‖t‖) :=
    Complex.fixedRealPartLine_log_norm_le_linear hσ t
  have hB_nonneg : 0 ≤ B :=
    div_nonneg zero_le_one hσ.le
  have hI_const : ‖I‖ ≤ B :=
    Complex.fixedRealPartLine_inv_two_mul_norm_le_const hσ t
  have hI : ‖I‖ ≤ B * (1 + ‖t‖) := by
    calc
      ‖I‖ ≤ B := hI_const
      _ = B * 1 := (mul_one B).symm
      _ ≤ B * (1 + ‖t‖) :=
        mul_le_mul_of_nonneg_left (Real.one_le_one_add_norm t) hB_nonneg
  have hsum :
      ‖L‖ + ‖I‖ ≤ A * (1 + ‖t‖) + B * (1 + ‖t‖) :=
    add_le_add hL hI
  have hfactor :
      A * (1 + ‖t‖) + B * (1 + ‖t‖) =
        (A + B) * (1 + ‖t‖) :=
    (add_mul A B (1 + ‖t‖)).symm
  calc
    ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤ ‖L‖ + ‖I‖ :=
      htriangle
    _ ≤ A * (1 + ‖t‖) + B * (1 + ‖t‖) :=
      hsum
    _ = (A + B) * (1 + ‖t‖) :=
      hfactor

/-- The differentiated Binet remainder has linear growth on every positive
fixed-real-part vertical line. -/
theorem Complex.GammaLogDerivativeFixedVerticalRemainder_linear_bound
    {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ t : ℝ,
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
        |‖(2 : ℂ)‖ *
          ∫ u : ℝ in Set.Ioi (0 : ℝ),
            (1 / σ ^ 2) *
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))| *
          (1 + ‖t‖) := by
  intro t
  let C : ℝ :=
    ‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / σ ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))
  have hconst :
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤ C :=
    Complex.GammaLogDerivativeFixedVerticalRemainder_norm_le_const hσ t
  have hC_abs : C ≤ |C| :=
    le_abs_self C
  have hC_abs_nonneg : 0 ≤ |C| :=
    abs_nonneg C
  have hlinear :
      |C| ≤ |C| * (1 + ‖t‖) := by
    calc
      |C| = |C| * 1 := by
        exact (mul_one |C|).symm
      _ ≤ |C| * (1 + ‖t‖) :=
        mul_le_mul_of_nonneg_left
          (Real.one_le_one_add_norm t) hC_abs_nonneg
  calc
    ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤ C :=
      hconst
    _ ≤ |C| := hC_abs
    _ ≤ |C| * (1 + ‖t‖) :=
      hlinear

/-- Fixed-positive-real-part logarithmic derivative of Gamma has linear growth
on vertical lines, with the Binet coherence package supplying the identity. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant σ *
          (1 + ‖t‖) := by
  let M : ℝ := (|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ
  let R : ℝ :=
    |‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / σ ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  have hmain_pow :
      ∀ t : ℝ,
        ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤
          M * (1 + ‖t‖) ^ (1 : ℕ) := by
    intro t
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤
          M * (1 + ‖t‖) :=
      Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound hσ t
    have hpow :
        (1 + ‖t‖) ^ (1 : ℕ) = (1 + ‖t‖ : ℝ) :=
      pow_one (1 + ‖t‖)
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.GammaLogDerivativeFixedVerticalMain σ t‖ ≤ M * x)
        hpow.symm
        hmain
  have hremainder_pow :
      ∀ t : ℝ,
        ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
          R * (1 + ‖t‖) ^ (1 : ℕ) := by
    intro t
    have hremainder :
        ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤
          R * (1 + ‖t‖) :=
      Complex.GammaLogDerivativeFixedVerticalRemainder_linear_bound hσ t
    have hpow :
        (1 + ‖t‖) ^ (1 : ℕ) = (1 + ‖t‖ : ℝ) :=
      pow_one (1 + ‖t‖)
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.GammaLogDerivativeFixedVerticalRemainder σ t‖ ≤ R * x)
        hpow.symm
        hremainder
  intro t
  have hbound_pow :
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        (M + R) * (1 + ‖t‖) ^ (1 : ℕ) :=
    Complex.Gamma_logDerivative_fixedRealPartLine_bound_of_main_remainder
      hcoh hσ 1 M R hmain_pow hremainder_pow t
  have hpow :
      (1 + ‖t‖) ^ (1 : ℕ) = (1 + ‖t‖ : ℝ) :=
    pow_one (1 + ‖t‖)
  have hlinear :
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        (M + R) * (1 + ‖t‖) :=
    Eq.subst
      (motive := fun x : ℝ =>
        ‖deriv Complex.Gamma (σ + t * Complex.I) /
            Complex.Gamma (σ + t * Complex.I)‖ ≤
          (M + R) * x)
      hpow
      hbound_pow
  have hconstant :
      M + R =
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant σ :=
    rfl
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖deriv Complex.Gamma (σ + t * Complex.I) /
            Complex.Gamma (σ + t * Complex.I)‖ ≤
          x * (1 + ‖t‖))
      hconstant
      hlinear

/-- Fixed-positive-real-part logarithmic derivative of Gamma has linear growth
on vertical lines, with the explicit majorant packaged as its owner constant. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_positiveLineConstant
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ : 0 < σ) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant σ *
          (1 + ‖t‖) := by
  intro t
  exact
    Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound
      hcoh hσ t

/-- One-step fixed-line shift for Gamma logarithmic-derivative bounds, in a
form that consumes an arbitrary bound on the shifted line. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_one_bound
    {σ B : ℝ}
    (hσ_ne_zero : σ ≠ 0)
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n)
    (hshift_bound :
      ∀ t : ℝ,
        ‖deriv Complex.Gamma ((σ + 1 : ℝ) + t * Complex.I) /
            Complex.Gamma ((σ + 1 : ℝ) + t * Complex.I)‖ ≤
          B * (1 + ‖t‖)) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        (B + |σ|⁻¹) * (1 + ‖t‖) := by
  intro t
  let s : ℂ := σ + t * Complex.I
  have hline_shift :
      s + 1 = ((σ + 1 : ℝ) + t * Complex.I : ℂ) := by
    calc
      s + 1 = ((σ : ℂ) + t * Complex.I) + 1 := by
        exact congrArg (fun z : ℂ => z + 1) rfl
      _ = ((σ : ℂ) + 1) + t * Complex.I := by
        exact add_right_comm (σ : ℂ) (t * Complex.I) 1
      _ = ((σ + 1 : ℝ) + t * Complex.I : ℂ) := by
        have hone : (((1 : ℝ) : ℂ)) = (1 : ℂ) :=
          rfl
        have hreal :
            ((σ : ℂ) + 1) = ((σ + 1 : ℝ) : ℂ) :=
          (congrArg (fun z : ℂ => (σ : ℂ) + z) hone.symm).trans
            (Complex.ofReal_add σ 1).symm
        exact congrArg (fun z : ℂ => z + t * Complex.I)
          hreal
  have hshift_here :
      ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ ≤
        B * (1 + ‖t‖) := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
            B * (1 + ‖t‖))
        hline_shift.symm
        (hshift_bound t)
  have hs0 : s ≠ 0 := by
    intro hs0_eq
    have hre :
        s.re = (0 : ℂ).re :=
      congrArg Complex.re hs0_eq
    have hs_re : s.re = σ :=
      Complex.fixedRealPartLine_re σ t
    have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
      Complex.zero_re
    exact hσ_ne_zero (hs_re.symm.trans (hre.trans hzero_re))
  have hrec :
      deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) =
        deriv Complex.Gamma s / Complex.Gamma s + 1 / s :=
    Complex.Gamma_logDerivative_add_one (s := s) hs0 (hnot_pole t)
  have hsolve :
      deriv Complex.Gamma s / Complex.Gamma s =
        deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) - 1 / s :=
    (eq_sub_iff_add_eq).mpr hrec.symm
  have htriangle :
      ‖deriv Complex.Gamma s / Complex.Gamma s‖ ≤
        ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
          ‖1 / s‖ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤
            ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
              ‖1 / s‖)
        hsolve.symm
        (norm_sub_le
          (deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1))
          (1 / s))
  have hinv_bound :
      ‖1 / s‖ ≤ |σ|⁻¹ * (1 + ‖t‖) := by
    have hone_div :
        ‖1 / s‖ = ‖s⁻¹‖ := by
      exact congrArg norm (one_div s)
    have hraw :
        ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤
          |σ|⁻¹ * (1 + ‖t‖) :=
      Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
        hσ_ne_zero t
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ |σ|⁻¹ * (1 + ‖t‖))
        hone_div.symm
        hraw
  have hsum :
      ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
          ‖1 / s‖ ≤
        B * (1 + ‖t‖) + |σ|⁻¹ * (1 + ‖t‖) :=
    add_le_add hshift_here hinv_bound
  have hfactor :
      B * (1 + ‖t‖) + |σ|⁻¹ * (1 + ‖t‖) =
        (B + |σ|⁻¹) * (1 + ‖t‖) :=
    (add_mul B |σ|⁻¹ (1 + ‖t‖)).symm
  exact htriangle.trans (hsum.trans_eq hfactor)


/-- Finite fixed-line shift for Gamma logarithmic-derivative bounds.

If some natural right-shift of the fixed real part is positive and the original
vertical line avoids the ordinary Gamma pole locus, then the original line has
linear growth for `Γ'/Γ`. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_nat
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (N : ℕ)
    (hσ_shift_pos : 0 < σ + (N : ℝ))
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalShiftConstant σ N *
          (1 + ‖t‖) := by
  induction N generalizing σ with
  | zero =>
      intro t
      have hσ_pos : 0 < σ := by
        have hzero : σ + ((0 : ℕ) : ℝ) = σ := by
          have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
            Nat.cast_zero
          exact (congrArg (fun x : ℝ => σ + x) hcast).trans (add_zero σ)
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hzero
            hσ_shift_pos
      have hpositive :
          ‖deriv Complex.Gamma (σ + t * Complex.I) /
              Complex.Gamma (σ + t * Complex.I)‖ ≤
            Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant σ *
              (1 + ‖t‖) :=
        Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_positiveLineConstant
          hcoh hσ_pos t
      exact hpositive
  | succ N ih =>
      intro t
      have htail_pos : 0 < (σ + 1) + (N : ℝ) := by
        have hrewrite :
            σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) :=
          Complex.real_add_one_add_nat_eq_add_succ σ N
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hrewrite
            hσ_shift_pos
      have htail_pole :
          ∀ t : ℝ, ∀ n : ℕ,
            ((σ + 1 : ℝ) + t * Complex.I : ℂ) ≠ -n :=
        Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus
          hnot_pole
      have htail_bound :
          ∀ t : ℝ,
            ‖deriv Complex.Gamma ((σ + 1 : ℝ) + t * Complex.I) /
                Complex.Gamma ((σ + 1 : ℝ) + t * Complex.I)‖ ≤
              Complex.GammaLogDerivativeFixedVerticalShiftConstant (σ + 1) N *
                (1 + ‖t‖) :=
        ih htail_pos htail_pole
      have hσ_ne_zero : σ ≠ 0 :=
        Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
          hnot_pole
      exact
        Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_one_bound
          hσ_ne_zero hnot_pole htail_bound t


/-- One-step fixed-line shift for Gamma logarithmic-derivative bounds.

If the line of real part `σ + 1` is already controlled by Binet's positive
half-plane estimate and the line of real part `σ` avoids Gamma poles, then the
line of real part `σ` has the same linear growth, up to the reciprocal term
from the Gamma recurrence. -/
theorem Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_one
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    {σ : ℝ}
    (hσ_shift_pos : 0 < σ + 1)
    (hσ_ne_zero : σ ≠ 0)
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ,
      ‖deriv Complex.Gamma (σ + t * Complex.I) /
          Complex.Gamma (σ + t * Complex.I)‖ ≤
        (((|Real.log (σ + 1)| + ((σ + 1) + 1) + Real.pi) +
            1 / (σ + 1)) +
          |‖(2 : ℂ)‖ *
            ∫ u : ℝ in Set.Ioi (0 : ℝ),
              (1 / (σ + 1) ^ 2) *
                (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))| +
          |σ|⁻¹) *
          (1 + ‖t‖) := by
  intro t
  let s : ℂ := σ + t * Complex.I
  let τ : ℝ := σ + 1
  let B : ℝ :=
    (((|Real.log τ| + (τ + 1) + Real.pi) + 1 / τ) +
      |‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / τ ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|)
  let R : ℝ := |σ|⁻¹
  have hline_shift :
      s + 1 = (τ + t * Complex.I : ℂ) := by
    calc
      s + 1 = ((σ : ℂ) + t * Complex.I) + 1 := by
        exact congrArg (fun z : ℂ => z + 1) rfl
      _ = ((σ : ℂ) + 1) + t * Complex.I := by
        exact add_right_comm (σ : ℂ) (t * Complex.I) 1
      _ = (τ + t * Complex.I : ℂ) := by
        have hone : (((1 : ℝ) : ℂ)) = (1 : ℂ) :=
          rfl
        have hreal :
            ((σ : ℂ) + 1) = (τ : ℂ) :=
          (congrArg (fun z : ℂ => (σ : ℂ) + z) hone.symm).trans
            (Complex.ofReal_add σ 1).symm
        exact congrArg (fun z : ℂ => z + t * Complex.I)
          hreal
  have hshift_bound :
      ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ ≤
        B * (1 + ‖t‖) := by
    have hpositive :
        ‖deriv Complex.Gamma (τ + t * Complex.I) /
            Complex.Gamma (τ + t * Complex.I)‖ ≤
          B * (1 + ‖t‖) :=
      Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound
        hcoh hσ_shift_pos t
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
            B * (1 + ‖t‖))
        hline_shift.symm
        hpositive
  have hrec :
      deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) =
        deriv Complex.Gamma s / Complex.Gamma s + 1 / s :=
    Complex.Gamma_logDerivative_add_one
      (s := s)
      (by
        intro hs0
        have hre :
            s.re = (0 : ℂ).re :=
          congrArg Complex.re hs0
        have hs_re : s.re = σ :=
          Complex.fixedRealPartLine_re σ t
        have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
          Complex.zero_re
        exact hσ_ne_zero (hs_re.symm.trans (hre.trans hzero_re)))
      (hnot_pole t)
  have hsolve :
      deriv Complex.Gamma s / Complex.Gamma s =
        deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1) - 1 / s :=
    (eq_sub_iff_add_eq).mpr hrec.symm
  have htriangle :
      ‖deriv Complex.Gamma s / Complex.Gamma s‖ ≤
        ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
          ‖1 / s‖ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤
            ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
              ‖1 / s‖)
        hsolve.symm
        (norm_sub_le
          (deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1))
          (1 / s))
  have hinv_bound :
      ‖1 / s‖ ≤ R * (1 + ‖t‖) := by
    have hone_div :
        ‖1 / s‖ = ‖s⁻¹‖ := by
      exact congrArg norm (one_div s)
    have hraw :
        ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤ R * (1 + ‖t‖) :=
      Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
        hσ_ne_zero t
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ R * (1 + ‖t‖))
        hone_div.symm
        hraw
  have hsum :
      ‖deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)‖ +
          ‖1 / s‖ ≤
        B * (1 + ‖t‖) + R * (1 + ‖t‖) :=
    add_le_add hshift_bound hinv_bound
  have hfactor :
      B * (1 + ‖t‖) + R * (1 + ‖t‖) =
        (B + R) * (1 + ‖t‖) :=
    (add_mul B R (1 + ‖t‖)).symm
  exact htriangle.trans (hsum.trans_eq hfactor)


/-- Linear-growth constant for the finite-shift Binet main term. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
    (σ : ℝ) : ℕ → ℝ
  | 0 => (|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ
  | Nat.succ N =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
        (σ + 1) N + |σ|⁻¹

/-- The positive-line Binet-main linear-growth constant is nonnegative. -/
theorem Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg
    {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ (|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ := by
  have hlog_nonneg : 0 ≤ |Real.log σ| :=
    abs_nonneg (Real.log σ)
  have hσ_one_nonneg : 0 ≤ σ + 1 :=
    add_nonneg hσ.le zero_le_one
  have hpi_nonneg : 0 ≤ Real.pi :=
    Real.pi_pos.le
  have hsum_left : 0 ≤ |Real.log σ| + (σ + 1) + Real.pi :=
    add_nonneg (add_nonneg hlog_nonneg hσ_one_nonneg) hpi_nonneg
  have hinv_nonneg : 0 ≤ 1 / σ :=
    div_nonneg zero_le_one hσ.le
  exact add_nonneg hsum_left hinv_nonneg

/-- The finite-shift Binet-main linear-growth constant is nonnegative, whenever
the terminal shifted line lies in the positive half-plane. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
    {σ : ℝ} :
    ∀ N : ℕ,
      0 < σ + (N : ℝ) →
        0 ≤
          Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
            σ N
  | 0, hσ => by
      have hzero : σ + ((0 : ℕ) : ℝ) = σ := by
        have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
          Nat.cast_zero
        exact (congrArg (fun x : ℝ => σ + x) hcast).trans (add_zero σ)
      have hσ_pos : 0 < σ :=
        Eq.subst
          (motive := fun x : ℝ => 0 < x)
          hzero
          hσ
      exact
        Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg
          hσ_pos
  | Nat.succ N, hσ => by
      have htail_pos : 0 < (σ + 1) + (N : ℝ) := by
        have hrewrite :
            σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) :=
          Complex.real_add_one_add_nat_eq_add_succ σ N
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hrewrite
            hσ
      have htail :
          0 ≤
            Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
              (σ + 1) N :=
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
          N htail_pos
      have hinv : 0 ≤ |σ|⁻¹ :=
        inv_nonneg.mpr (abs_nonneg σ)
      exact add_nonneg htail hinv

/-- Linear-growth constant for the finite-shift Binet remainder. -/
noncomputable def Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
    (σ : ℝ) : ℕ → ℝ
  | 0 =>
      |‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / σ ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  | Nat.succ N =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
        (σ + 1) N

/-- The finite-shift Binet remainder linear-growth constant is nonnegative. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant_nonneg
    (σ : ℝ) :
    ∀ N : ℕ,
      0 ≤
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
          σ N := by
  intro N
  induction N generalizing σ with
  | zero =>
      exact abs_nonneg
        (‖(2 : ℂ)‖ *
          ∫ u : ℝ in Set.Ioi (0 : ℝ),
            (1 / σ ^ 2) *
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)))
  | succ N ih =>
      exact ih (σ + 1)

/-- The finite-shift Binet main term has linear growth whenever the final
shifted line is in the positive half-plane and the original line avoids Gamma
poles. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatMain_linear_bound
    {σ : ℝ}
    (N : ℕ)
    (hσ_shift_pos : 0 < σ + (N : ℝ))
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ,
      ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N t‖ ≤
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant σ N *
          (1 + ‖t‖) := by
  induction N generalizing σ with
  | zero =>
      intro t
      have hσ_pos : 0 < σ := by
        have hzero : σ + ((0 : ℕ) : ℝ) = σ := by
          have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
            Nat.cast_zero
          exact (congrArg (fun x : ℝ => σ + x) hcast).trans (add_zero σ)
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hzero
            hσ_shift_pos
      exact Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound hσ_pos t
  | succ N ih =>
      intro t
      let s : ℂ := σ + t * Complex.I
      have htail_pos : 0 < (σ + 1) + (N : ℝ) := by
        have hrewrite :
            σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) :=
          Complex.real_add_one_add_nat_eq_add_succ σ N
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hrewrite
            hσ_shift_pos
      have htail_pole :
          ∀ t : ℝ, ∀ n : ℕ,
            ((σ + 1 : ℝ) + t * Complex.I : ℂ) ≠ -n :=
        Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus
          hnot_pole
      have hshift_main :
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              (σ + 1) N t‖ ≤
            Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
              (σ + 1) N *
              (1 + ‖t‖) :=
        ih htail_pos htail_pole t
      have hσ_ne_zero : σ ≠ 0 :=
        Complex.fixedRealPartLine_realPart_ne_zero_of_ne_Gamma_zero_locus
          hnot_pole
      have hinv :
          ‖1 / s‖ ≤ |σ|⁻¹ * (1 + ‖t‖) := by
        have hone_div :
            ‖1 / s‖ = ‖s⁻¹‖ := by
          exact congrArg norm (one_div s)
        have hraw :
            ‖((σ + t * Complex.I : ℂ)⁻¹)‖ ≤
              |σ|⁻¹ * (1 + ‖t‖) :=
          Complex.fixedRealPartLine_inv_norm_le_abs_re_inv_mul_one_add_norm
            hσ_ne_zero t
        exact
          Eq.subst
            (motive := fun x : ℝ => x ≤ |σ|⁻¹ * (1 + ‖t‖))
            hone_div.symm
            hraw
      have htriangle :
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ (N + 1) t‖ ≤
            ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                (σ + 1) N t‖ + ‖1 / s‖ :=
        norm_sub_le
          (Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            (σ + 1) N t)
          (1 / s)
      have hsum :
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                (σ + 1) N t‖ + ‖1 / s‖ ≤
            Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
                (σ + 1) N *
                (1 + ‖t‖) +
              |σ|⁻¹ * (1 + ‖t‖) :=
        add_le_add hshift_main hinv
      have hfactor :
          Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
                (σ + 1) N *
                (1 + ‖t‖) +
              |σ|⁻¹ * (1 + ‖t‖) =
            (Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
                (σ + 1) N + |σ|⁻¹) *
              (1 + ‖t‖) :=
        (add_mul
          (Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
            (σ + 1) N)
          |σ|⁻¹
          (1 + ‖t‖)).symm
      exact htriangle.trans (hsum.trans_eq hfactor)

/-- The finite-shift Binet remainder has linear growth whenever the final
shifted line is in the positive half-plane and the original line avoids Gamma
poles. -/
theorem Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_linear_bound
    {σ : ℝ}
    (N : ℕ)
    (hσ_shift_pos : 0 < σ + (N : ℝ))
    (hnot_pole :
      ∀ t : ℝ, ∀ n : ℕ,
        (σ + t * Complex.I : ℂ) ≠ -n) :
    ∀ t : ℝ,
      ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N t‖ ≤
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
          σ N * (1 + ‖t‖) := by
  induction N generalizing σ with
  | zero =>
      intro t
      have hσ_pos : 0 < σ := by
        have hzero : σ + ((0 : ℕ) : ℝ) = σ := by
          have hcast : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
            Nat.cast_zero
          exact (congrArg (fun x : ℝ => σ + x) hcast).trans (add_zero σ)
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hzero
            hσ_shift_pos
      exact
        Complex.GammaLogDerivativeFixedVerticalRemainder_linear_bound
          hσ_pos t
  | succ N ih =>
      intro t
      have htail_pos : 0 < (σ + 1) + (N : ℝ) := by
        have hrewrite :
            σ + ((N + 1 : ℕ) : ℝ) = (σ + 1) + (N : ℝ) :=
          Complex.real_add_one_add_nat_eq_add_succ σ N
        exact
          Eq.subst
            (motive := fun x : ℝ => 0 < x)
            hrewrite
            hσ_shift_pos
      have htail_pole :
          ∀ t : ℝ, ∀ n : ℕ,
            ((σ + 1 : ℝ) + t * Complex.I : ℂ) ≠ -n :=
        Complex.fixedRealPartLine_shift_one_ne_Gamma_zero_locus
          hnot_pole
      exact ih htail_pos htail_pole t

end

end LFunctions
end Boundary
