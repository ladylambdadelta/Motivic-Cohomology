import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetKernelBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Binet formula and kernel estimates

This file owns Binet's second logarithmic formula and the real majorant
estimates for its kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The derivative kernel obtained by differentiating
`arctan ((t : ℂ) / w)` in Binet's second-formula remainder. -/
noncomputable def Complex.binetSecondFormulaDerivativeKernel
    (t : ℝ) (w : ℂ) : ℂ :=
  (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The candidate derivative of the Binet second-formula remainder after
differentiating under the integral sign. -/
noncomputable def Complex.binetSecondFormulaRemainderDerivative
    (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetSecondFormulaDerivativeKernel t w

/-- Branch-correct Binet formula on the open right half-plane.

The global Abel-Plana output is an analytic logarithm branch, not Lean's
principal `Complex.log (Complex.Gamma w)`. -/
theorem Complex.Gamma_binetSecondFormula_branchExponential :
    ∀ {w : ℂ},
      0 < w.re →
        Complex.exp (Complex.binetLogGammaBranch w) =
          Complex.Gamma w := by
  intro w hw
  exact
    Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana w hw

/-- The Binet main term is real-valued on the positive real axis. -/
theorem Complex.binetLogGammaMainTerm_posReal_im_eq_zero
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetLogGammaMainTerm (x : ℂ)).im = 0 := by
  have hlog :
      Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  unfold Complex.binetLogGammaMainTerm
  exact congrArg (fun z : ℂ => z - ((1 / 2 : ℂ) * Complex.log (x : ℂ)) - (x : ℂ)) hlog
  norm_num

/-- The Binet arctangent kernel is real-valued on the positive real axis. -/
theorem Complex.binetSecondFormulaKernel_posReal_im_eq_zero
    {x t : ℝ}
    (hx : 0 < x)
    (ht : 0 < t) :
    (Complex.arctan ((t : ℂ) / (x : ℂ)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)).im = 0 := by
  have harg :
      (t : ℂ) / (x : ℂ) = ((t / x : ℝ) : ℂ) := by
    exact (Complex.ofReal_div t x).symm
  have harctan :
      Complex.arctan ((t : ℂ) / (x : ℂ)) =
        ((Real.arctan (t / x) : ℝ) : ℂ) := by
    calc
      Complex.arctan ((t : ℂ) / (x : ℂ)) =
          Complex.arctan ((t / x : ℝ) : ℂ) := by
        exact congrArg Complex.arctan harg
      _ = ((Real.arctan (t / x) : ℝ) : ℂ) :=
        (Complex.ofReal_arctan (t / x)).symm
  have hden :
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
        ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
    exact
      by
        calc
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
              ((Real.exp ((2 : ℝ) * Real.pi * t) : ℝ) : ℂ) - 1 := by
            exact congrArg (fun z : ℂ => z - 1) (Complex.ofReal_exp _)
          _ = ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
            rfl
  exact congrArg2 (fun a b : ℂ => a / b) harctan hden
  norm_num

/-- The Binet second-formula remainder is real-valued on the positive real
axis. -/
theorem Complex.binetSecondFormulaRemainder_posReal_im_eq_zero
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetSecondFormulaRemainder (x : ℂ)).im = 0 := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / (x : ℂ)) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK_integrable :
      Integrable K (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
    exact
      Complex.binetSecondFormula_arctanKernel_integrable_owner
        (w := (x : ℂ)) hx
  have hK_im_zero :
      ∀ᵐ t ∂Measure.restrict volume (Set.Ioi (0 : ℝ)),
        (K t).im = 0 := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with t ht
    exact
      Complex.binetSecondFormulaKernel_posReal_im_eq_zero
        hx ht
  have hintegral_im_zero :
      (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im = 0 := by
    have him_integral :
        ∫ t : ℝ in Set.Ioi (0 : ℝ), (K t).im =
          (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im := by
      exact integral_im hK_integrable
    have him_integrand_zero :
        ∫ t : ℝ in Set.Ioi (0 : ℝ), (K t).im = 0 := by
      exact integral_eq_zero_of_ae hK_im_zero
    exact Eq.trans him_integral.symm him_integrand_zero
  unfold Complex.binetSecondFormulaRemainder
  change (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im = 0
  have hmul_im :
      (2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im =
        2 * (∫ t : ℝ in Set.Ioi (0 : ℝ), K t).im := by
    exact Complex.mul_im _ _
  exact hmul_im.trans (by
    norm_num [hintegral_im_zero])
  norm_num [hintegral_im_zero]

/-- The Binet logarithm branch is real-valued on the positive real axis. -/
theorem Complex.binetLogGammaBranch_posReal_im_eq_zero_owner
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.binetLogGammaBranch (x : ℂ)).im = 0 := by
  unfold Complex.binetLogGammaBranch
  have hmain := Complex.binetLogGammaMainTerm_posReal_im_eq_zero hx
  have hrem := Complex.binetSecondFormulaRemainder_posReal_im_eq_zero hx
  exact
    by
      calc
        (Complex.binetLogGammaMainTerm (x : ℂ) +
            Complex.binetSecondFormulaRemainder (x : ℂ)).im =
            Complex.binetLogGammaMainTerm (x : ℂ).im +
              Complex.binetSecondFormulaRemainder (x : ℂ).im := by
          exact Complex.add_im _ _
        _ = 0 := by
          linarith
  norm_num

/-- On the positive real axis, the analytic Binet branch agrees with Lean's
principal logarithm of Gamma. -/
theorem Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner
    {x : ℝ}
    (hx : 0 < x) :
    Complex.binetLogGammaBranch (x : ℂ) =
      Complex.log (Complex.Gamma (x : ℂ)) := by
  have hbranch_exp :
      Complex.exp (Complex.binetLogGammaBranch (x : ℂ)) =
        Complex.Gamma (x : ℂ) :=
    Complex.Gamma_binetSecondFormula_branchExponential
      (w := (x : ℂ)) hx
  have hgamma_pos : 0 < Real.Gamma x :=
    Real.Gamma_pos_of_pos hx
  have hgamma_real :
      Complex.Gamma (x : ℂ) = (Real.Gamma x : ℂ) :=
    Complex.Gamma_ofReal x
  have hlog_gamma :
      ((Real.log (Real.Gamma x) : ℝ) : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) := by
    exact by
      have h' : Complex.Gamma (x : ℂ) = ((Real.Gamma x : ℝ) : ℂ) := hgamma_real
      exact h'.symm ▸ (Complex.ofReal_log hgamma_pos.le).symm
  have hlog_im :
      (Complex.log (Complex.Gamma (x : ℂ))).im = 0 := by
    exact congrArg Complex.im hlog_gamma
  have hbranch_im :
      (Complex.binetLogGammaBranch (x : ℂ)).im = 0 :=
    Complex.binetLogGammaBranch_posReal_im_eq_zero_owner hx
  have hlog_exp :
      Complex.exp (Complex.log (Complex.Gamma (x : ℂ))) =
        Complex.Gamma (x : ℂ) :=
    Complex.exp_log
      (by
        exact hgamma_real.symm ▸ (Complex.ofReal_ne_zero.mpr (ne_of_gt hgamma_pos)))
  exact
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by exact hbranch_im ▸ neg_lt_zero.mpr Real.pi_pos)
      (by exact hbranch_im ▸ Real.pi_pos.le)
      (by exact hlog_im ▸ neg_lt_zero.mpr Real.pi_pos)
      (by exact hlog_im ▸ Real.pi_pos.le)
      (Eq.trans hbranch_exp hlog_exp.symm)

/-- Positive-real principal-log normalization for Binet's second formula.

This is a real-axis branch comparison theorem.  It is separate from the global
open-half-plane Abel-Plana output, which is the branch-exponential theorem
above. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  have hbranch :
      Complex.binetLogGammaBranch (x : ℂ) =
        Complex.log (Complex.Gamma (x : ℂ)) :=
    Complex.binetLogGammaBranch_eq_principalLog_Gamma_of_posReal_owner hx
  exact hbranch.symm

/-- The principal complex arctangent has derivative `1 / (1 + z^2)` at points
where its defining logarithm is differentiable.  The extra `slitPlane`
hypothesis is essential for the principal branch of `Complex.log`. -/
theorem Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
    {z : ℂ}
    (hzI : z ≠ Complex.I)
    (hznegI : z ≠ -Complex.I)
    (hzslit :
      (1 + z * Complex.I) / (1 - z * Complex.I) ∈ Complex.slitPlane) :
    HasDerivAt
      Complex.arctan
      ((1 : ℂ) / (1 + z ^ 2)) z := by
  have hnum_ne : 1 + z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          exact (mul_div_cancel_right₀ z Complex.I_ne_zero).symm
        _ = (-1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = -1 := by
            exact add_eq_zero_iff_eq_neg.mp hzero
          exact congrArg (fun u : ℂ => u / Complex.I) hzI_eq
        _ = Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hzI hz_eq
  have hden_ne : 1 - z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = -Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          exact (mul_div_cancel_right₀ z Complex.I_ne_zero).symm
        _ = (1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = 1 := by
            exact sub_eq_zero.mp hzero
          exact congrArg (fun u : ℂ => u / Complex.I) hzI_eq
        _ = -Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hznegI hz_eq
  let q : ℂ → ℂ :=
    fun u : ℂ => (1 + u * Complex.I) / (1 - u * Complex.I)
  have hq :
      HasDerivAt q
        ((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) z := by
    have hnum :
        HasDerivAt (fun u : ℂ => 1 + u * Complex.I) Complex.I z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
    have hden :
        HasDerivAt (fun u : ℂ => 1 - u * Complex.I) (-Complex.I) z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
    have hdiv := hnum.div hden hden_ne
    exact by
      exact hdiv
  have hlog :
      HasDerivAt
        (fun u : ℂ => Complex.log (q u))
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hq.clog hzslit
  have hscaled :
      HasDerivAt
        (fun u : ℂ => (-Complex.I / 2) * Complex.log (q u))
        ((-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I)))) z :=
    hlog.const_mul (-Complex.I / 2)
  have halg :
      (-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        (1 : ℂ) / (1 + z ^ 2) := by
    have hprod_ne : 1 + z ^ 2 ≠ 0 := by
      have hfactor :
          (1 - z * Complex.I) * (1 + z * Complex.I) = 1 + z ^ 2 := by
        ring_nf
      intro hzero
      exact (mul_ne_zero hden_ne hnum_ne) (hfactor.trans hzero)
    field_simp [hnum_ne, hden_ne, hprod_ne]
    ring_nf
  exact by
    exact hscaled

/-- A point in the open right half-plane is nonzero. -/
theorem Complex.ne_zero_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ≠ 0 := by
  intro hw
  have hre_zero : w.re = 0 := by
    exact congrArg Complex.re hw
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq hre_zero)

/-- Adding a purely imaginary number to a point in the open right half-plane
cannot give zero. -/
theorem Complex.add_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w + (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w + (t : ℂ) * Complex.I).re = 0 := by
    exact congrArg Complex.re hzero
  have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re := by
    calc
      (w + (t : ℂ) * Complex.I).re = w.re + ((t : ℂ) * Complex.I).re := by
        exact Complex.add_re w ((t : ℂ) * Complex.I)
      _ = w.re := by
        have hmul : ((t : ℂ) * Complex.I).re = 0 := by
          calc
            ((t : ℂ) * Complex.I).re =
                (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
              exact Complex.mul_re _ _
            _ = 0 := by norm_num
        linarith
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- Subtracting a purely imaginary number from a point in the open right
half-plane cannot give zero. -/
theorem Complex.sub_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w - (t : ℂ) * Complex.I).re = 0 := by
    exact congrArg Complex.re hzero
  have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re := by
    calc
      (w - (t : ℂ) * Complex.I).re = w.re - ((t : ℂ) * Complex.I).re := by
        exact Complex.sub_re w ((t : ℂ) * Complex.I)
      _ = w.re := by
        have hmul : ((t : ℂ) * Complex.I).re = 0 := by
          calc
            ((t : ℂ) * Complex.I).re =
                (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
              exact Complex.mul_re _ _
            _ = 0 := by norm_num
        linarith
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- The algebraic denominator `w^2 + t^2` in the differentiated Binet kernel
does not vanish in the open right half-plane. -/
theorem Complex.binet_arctan_derivative_denominator_ne_zero
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  have hplus :
      w + (t : ℂ) * Complex.I ≠ 0 :=
    Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hminus :
      w - (t : ℂ) * Complex.I ≠ 0 :=
    Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hfactor :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) =
        w ^ 2 + (t : ℂ) ^ 2 := by
    calc
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I)
          = w ^ 2 - ((t : ℂ) * Complex.I) ^ 2 := by
            ring
      _ = w ^ 2 + (t : ℂ) ^ 2 := by
            have hI : (Complex.I : ℂ) ^ 2 = -1 := by
              exact Complex.I_mul_I
            nlinarith
  intro hzero
  have hprod_zero :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) = 0 :=
    hfactor.trans hzero
  exact
    (mul_ne_zero hplus hminus) hprod_zero

/-- A nonnegative real part gives a lower bound for the complex norm. -/
theorem Complex.re_le_norm_of_nonneg_re
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re) :
    z.re ≤ ‖z‖ := by
  have hre_abs_eq : |z.re| = z.re :=
    abs_of_nonneg hz_re_nonneg
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    exact Complex.abs_re_le_abs z
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      hre_abs_eq
      hre_abs_le_norm

/-- Adding a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_add_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z + (t : ℂ) * Complex.I‖ := by
  have hsum_re_nonneg : 0 ≤ (z + (t : ℂ) * Complex.I).re := by
    have hre : (z + (t : ℂ) * Complex.I).re = z.re := by
      calc
        (z + (t : ℂ) * Complex.I).re = z.re + ((t : ℂ) * Complex.I).re := by
          exact Complex.add_re z ((t : ℂ) * Complex.I)
        _ = z.re := by
          have hmul : ((t : ℂ) * Complex.I).re = 0 := by
            calc
              ((t : ℂ) * Complex.I).re =
                  (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
                exact Complex.mul_re _ _
              _ = 0 := by norm_num
          linarith
    exact hre ▸ hz_re_nonneg
  have hnorm :
      (z + (t : ℂ) * Complex.I).re ≤
        ‖z + (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hsum_re_nonneg
  have hre :
      (z + (t : ℂ) * Complex.I).re = z.re := by
    calc
      (z + (t : ℂ) * Complex.I).re = z.re + ((t : ℂ) * Complex.I).re := by
        exact Complex.add_re z ((t : ℂ) * Complex.I)
      _ = z.re := by
        have hmul : ((t : ℂ) * Complex.I).re = 0 := by
          calc
            ((t : ℂ) * Complex.I).re =
                (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
              exact Complex.mul_re _ _
            _ = 0 := by norm_num
        linarith
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z + (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Subtracting a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_sub_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z - (t : ℂ) * Complex.I‖ := by
  have hdiff_re_nonneg : 0 ≤ (z - (t : ℂ) * Complex.I).re := by
    have hre : (z - (t : ℂ) * Complex.I).re = z.re := by
      calc
        (z - (t : ℂ) * Complex.I).re = z.re - ((t : ℂ) * Complex.I).re := by
          exact Complex.sub_re z ((t : ℂ) * Complex.I)
        _ = z.re := by
          have hmul : ((t : ℂ) * Complex.I).re = 0 := by
            calc
              ((t : ℂ) * Complex.I).re =
                  (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
                exact Complex.mul_re _ _
              _ = 0 := by norm_num
          linarith
    exact hre ▸ hz_re_nonneg
  have hnorm :
      (z - (t : ℂ) * Complex.I).re ≤
        ‖z - (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hdiff_re_nonneg
  have hre :
      (z - (t : ℂ) * Complex.I).re = z.re := by
    calc
      (z - (t : ℂ) * Complex.I).re = z.re - ((t : ℂ) * Complex.I).re := by
        exact Complex.sub_re z ((t : ℂ) * Complex.I)
      _ = z.re := by
        have hmul : ((t : ℂ) * Complex.I).re = 0 := by
          calc
            ((t : ℂ) * Complex.I).re =
                (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
              exact Complex.mul_re _ _
            _ = 0 := by norm_num
        linarith
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z - (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Factoring `z^2 + t^2` into the two imaginary translates. -/
theorem Complex.add_mul_sub_real_mul_I_eq_sq_add_sq
    (z : ℂ)
    (t : ℝ) :
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I) =
      z ^ 2 + (t : ℂ) ^ 2 := by
  calc
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I)
        = z ^ 2 - ((t : ℂ) * Complex.I) ^ 2 := by
          ring
    _ = z ^ 2 + (t : ℂ) ^ 2 := by
          have hI : (Complex.I : ℂ) ^ 2 = -1 := by
            exact Complex.I_mul_I
          nlinarith

/-- Lower bound for the differentiated Binet denominator from a real-part
margin. -/
theorem Complex.binet_arctan_derivative_denominator_norm_lower
    {z : ℂ}
    {δ t : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_re : δ ≤ z.re) :
    δ ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
  have hz_re_nonneg : 0 ≤ z.re :=
    le_trans hδ_nonneg hδ_le_re
  have hplus :
      δ ≤ ‖z + (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_add_real_mul_I hz_re_nonneg t)
  have hminus :
      δ ≤ ‖z - (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_sub_real_mul_I hz_re_nonneg t)
  have hmul :
      δ * δ ≤
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    mul_le_mul hplus hminus
      hδ_nonneg
      (norm_nonneg (z + (t : ℂ) * Complex.I))
  have hnorm_mul :
      ‖(z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I)‖ =
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    norm_mul
      (z + (t : ℂ) * Complex.I)
      (z - (t : ℂ) * Complex.I)
  have hfactor :
      (z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I) =
        z ^ 2 + (t : ℂ) ^ 2 :=
    Complex.add_mul_sub_real_mul_I_eq_sq_add_sq z t
  have htarget :
      δ * δ ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ :=
    Eq.subst
      (motive := fun x : ℂ => δ * δ ≤ ‖x‖)
      hfactor
      (Eq.subst
        (motive := fun x : ℝ => δ * δ ≤ x)
        hnorm_mul.symm
        hmul)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖)
      (sq δ).symm
      htarget

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_I
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w + (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          exact (div_mul_cancel₀ (t : ℂ) hw_ne).symm
        _ = Complex.I * w := by
          exact congrArg (fun u : ℂ => u * w) h
    calc
      w + (t : ℂ) * Complex.I
          = w + (Complex.I * w) * Complex.I := by
            exact congrArg (fun u : ℂ => w + u * Complex.I) hmul
      _ = 0 := by
            ring_nf
  exact (Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `-I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_negI
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ -Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w - (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = -Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          exact (div_mul_cancel₀ (t : ℂ) hw_ne).symm
        _ = -Complex.I * w := by
          exact congrArg (fun u : ℂ => u * w) h
    calc
      w - (t : ℂ) * Complex.I
          = w - (-Complex.I * w) * Complex.I := by
            exact congrArg (fun u : ℂ => w - u * Complex.I) hmul
      _ = 0 := by
            ring_nf
  exact (Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- The denominator in the Cayley transform defining `Complex.arctan` is
nonzero away from the branch point `-I`. -/
theorem Complex.one_sub_mul_I_ne_zero_of_ne_negI
    {z : ℂ}
    (hz : z ≠ -Complex.I) :
    1 - z * Complex.I ≠ 0 := by
  intro hzero
  have hmul : z * Complex.I = 1 :=
    (sub_eq_zero.mp hzero).symm
  have harg : z = -Complex.I := by
    have hmul' := congrArg (fun u : ℂ => u * (-Complex.I)) hmul
    have hI : (Complex.I : ℂ) * Complex.I = -1 := by
      exact Complex.I_mul_I
    have hmul'' : z * Complex.I * (-Complex.I) = -Complex.I := by
      -- transport the identity through the right multiplication
      exact hmul'.trans (by ring_nf)
    exact hmul''
  exact hz harg

/-- Imaginary part of the Cayley transform used in the principal-log
definition of complex arctangent. -/
theorem Complex.arctan_cayley_im_eq
    (z : ℂ) :
    ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
      2 * z.re / Complex.normSq (1 - z * Complex.I) := by
  exact Complex.div_im _ _

/-- For `t > 0` and `0 < w.re`, the Cayley transform appearing in the
principal-log definition of `Complex.arctan ((t : ℂ) / w)` lies in the slit
plane, so the principal logarithm is differentiable there. -/
theorem Complex.binet_arctan_log_argument_mem_slitPlane
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have harg_ne_negI : (t : ℂ) / w ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have hden_ne :
      1 - ((t : ℂ) / w) * Complex.I ≠ 0 :=
    Complex.one_sub_mul_I_ne_zero_of_ne_negI harg_ne_negI
  have hq_im_pos :
      0 <
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) |>.im := by
    have ha_re_pos : 0 < ((t : ℂ) / w).re := by
      have hdivre :
          ((t : ℂ) / w).re =
            (t * w.re) / Complex.normSq w := by
        exact Complex.div_re (t : ℂ) w
      calc
        0 < (t * w.re) / Complex.normSq w := by
          exact div_pos
            (mul_pos (by exact ht) hw_re_pos)
            (Complex.normSq_pos.mpr hw_ne)
        _ = ((t : ℂ) / w).re := hdivre.symm
      exact
        div_pos
          (mul_pos (by exact ht) hw_re_pos)
          (Complex.normSq_pos.mpr hw_ne)
    have hcalc :
        (1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I) |>.im =
          2 * ((t : ℂ) / w).re /
            Complex.normSq (1 - ((t : ℂ) / w) * Complex.I) := by
      exact Complex.arctan_cayley_im_eq ((t : ℂ) / w)
    exact hcalc
    exact
      div_pos
        (mul_pos two_pos ha_re_pos)
        (Complex.normSq_pos.mpr hden_ne)
  have hnot_nonpos :
      ¬
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) ≤ 0 := by
    intro hle
    have him_zero :
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) |>.im = 0 := by
      exact (Complex.nonpos_iff.mp hle).2
    linarith
  exact (Complex.mem_slitPlane_iff_not_le_zero).2 hnot_nonpos

/-- The rational factor appearing in the Binet arctangent argument has the
expected derivative on the open right half-plane. -/
theorem Complex.binet_arctan_argument_derivative
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => (t : ℂ) / z)
      (-(t : ℂ) / w ^ 2) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  exact (hasDerivAt_inv hw_ne).const_mul (t : ℂ)

/-- The arctangent derivative needed for the Binet kernel after composing
`Complex.arctan` with `z ↦ (t : ℂ) / z` on the open right half-plane. -/
theorem Complex.arctan_t_div_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
      (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have harg_ne_I : (t : ℂ) / w ≠ Complex.I :=
    Complex.binet_arctan_argument_ne_I hw_re_pos
  have harg_ne_negI : (t : ℂ) / w ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have harg_slit :
      (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane :=
    Complex.binet_arctan_log_argument_mem_slitPlane ht hw_re_pos
  have h_inner :
      HasDerivAt
        (fun z : ℂ => (t : ℂ) / z)
        (-(t : ℂ) / w ^ 2) w := by
    exact Complex.binet_arctan_argument_derivative ht hw_re_pos
  have h_outer :
      HasDerivAt
        Complex.arctan
        ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) ((t : ℂ) / w) := by
    exact
      Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
        harg_ne_I harg_ne_negI harg_slit
  have hcomp :
      HasDerivAt
        (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
        (((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2)) w := by
    exact h_outer.comp w h_inner
  have hden_ne : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 :=
    Complex.binet_arctan_derivative_denominator_ne_zero hw_re_pos
  have halg :
      ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2) =
        -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2) := by
    field_simp [hw_ne, hden_ne]
    ring
  exact halg ▸ hcomp

/-- Pointwise derivative of the arctangent kernel in Binet's second-formula
remainder.  This is the branch-sensitive local analytic statement for
`Complex.arctan`, specialized to the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.arctan ((t : ℂ) / z) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Complex.binetSecondFormulaDerivativeKernel t w) w := by
  exact
    (Complex.arctan_t_div_hasDerivAt ht hw_re_pos).div_const
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- A small ball around a point in the open right half-plane remains in the
open right half-plane. -/
theorem Complex.exists_ball_subset_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z - w‖ < ε → 0 < z.re := by
  refine ⟨w.re / 2, half_pos hw_re_pos, ?_⟩
  intro z hz
  have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
    exact (abs_re_le_abs (z - w))
  have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
    lt_of_le_of_lt hre_le_norm hz
  have hre_lower : -(w.re / 2) < z.re - w.re :=
    (abs_lt.mp hre_abs_lt).1
  have hw_half_pos : 0 < w.re / 2 :=
    half_pos hw_re_pos
  have hhalf_lt_z : w.re / 2 < z.re := by
    calc
      w.re / 2 = w.re + (-(w.re / 2)) := by ring
      _ < w.re + (z.re - w.re) :=
        add_lt_add_left hre_lower w.re
      _ = z.re := by ring
  exact hw_half_pos.trans hhalf_lt_z

/-- A small ball around a point in the open right half-plane has the explicit
real-part margin `w.re / 2`. -/
theorem Complex.exists_ball_subset_re_ge_half
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z : ℂ, ‖z - w‖ < ε → w.re / 2 ≤ z.re := by
  refine ⟨w.re / 2, half_pos hw_re_pos, ?_⟩
  intro z hz
  have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
    exact (abs_re_le_abs (z - w))
  have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
    lt_of_le_of_lt hre_le_norm hz
  have hre_lower : -(w.re / 2) < z.re - w.re :=
    (abs_lt.mp hre_abs_lt).1
  have hhalf_lt_z : w.re / 2 < z.re := by
    calc
      w.re / 2 = w.re + (-(w.re / 2)) := by ring
      _ < w.re + (z.re - w.re) :=
        add_lt_add_left hre_lower w.re
      _ = z.re := by ring
  exact le_of_lt hhalf_lt_z

/-- The elementary division rearrangement used by the differentiated Binet
kernel majorant. -/
theorem Real.binet_derivativeKernel_div_sq_div_eq
    {δ d t : ℝ}
    (hδ_sq_ne : δ ^ 2 ≠ 0) :
    (t / δ ^ 2) / d = (1 / δ ^ 2) * (t / d) := by
  field_simp [hδ_sq_ne]
  ring

/-- Norm of the rational factor in the differentiated Binet kernel. -/
theorem Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖-(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2)‖ ≤ t / δ ^ 2 := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  have hδ_nonneg : 0 ≤ δ :=
    le_of_lt hδ_pos
  have hδ_sq_pos : 0 < δ ^ 2 :=
    sq_pos_of_pos hδ_pos
  have hD_lower : δ ^ 2 ≤ ‖D‖ := by
    exact
      Complex.binet_arctan_derivative_denominator_norm_lower
        hδ_nonneg hδ_le_re
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le hδ_sq_pos hD_lower
  have ht_norm : ‖(t : ℂ)‖ = t := by
    calc
      ‖(t : ℂ)‖ = |(t : ℝ)| := by
        exact Complex.norm_ofReal t
      _ = t := Real.norm_of_nonneg (le_of_lt ht)
  have hnorm :
      ‖-(t : ℂ) / D‖ = t / ‖D‖ := by
    calc
      ‖-(t : ℂ) / D‖ = ‖(t : ℂ)‖ / ‖D‖ := by
        exact norm_div _ _
      _ = t / ‖D‖ := by
        exact congrArg (fun x : ℝ => x / ‖D‖) ht_norm
  have hdiv :
      t / ‖D‖ ≤ t / δ ^ 2 :=
    div_le_div_of_nonneg_left
      (le_of_lt ht) hδ_sq_pos hD_lower
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ t / δ ^ 2)
      hnorm.symm
      hdiv

/-- Pointwise domination of the differentiated Binet kernel by the real Binet
majorant, with a real-part margin. -/
theorem Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤
      (1 / δ ^ 2) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  let E : ℂ := Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hrational :
      ‖-(t : ℂ) / D‖ ≤ t / δ ^ 2 :=
    Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
      hδ_pos hδ_le_re ht
  have hden_norm : ‖E‖ = d := by
    calc
      ‖E‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
        exact Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = d :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht
  have hd_nonneg : 0 ≤ d :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht)
  have hkernel_norm :
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := by
    calc
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
          ‖(-(t : ℂ) / D) / E‖ := by
        rfl
      _ = ‖-(t : ℂ) / D‖ / ‖E‖ := by
        exact norm_div _ _
      _ = ‖-(t : ℂ) / D‖ / d := by
        exact congrArg (fun x : ℝ => ‖-(t : ℂ) / D‖ / x) hden_norm
  have hdiv :
      ‖-(t : ℂ) / D‖ / d ≤ (t / δ ^ 2) / d :=
    div_le_div_of_nonneg_right hrational hd_nonneg
  have hδ_sq_ne : δ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hδ_pos)
  have hrearrange :
      (t / δ ^ 2) / d =
        (1 / δ ^ 2) * (t / d) :=
    Real.binet_derivativeKernel_div_sq_div_eq hδ_sq_ne
  calc
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := hkernel_norm
    _ ≤ (t / δ ^ 2) / d := hdiv
    _ = (1 / δ ^ 2) * (t / d) := hrearrange

/-- Local differentiability of the Binet arctangent kernel throughout a ball
inside the open right half-plane, in the form required by mathlib's
parameter-integral differentiation theorem. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∀ z : ℂ,
        ‖z - w‖ < ε →
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  exact
    Complex.binetSecondFormula_arctanKernel_hasDerivAt
      ht (hε_subset z hz)

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases Complex.exists_ball_subset_re_ge_half hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  let δ : ℝ := w.re / 2
  let g : ℝ → ℝ :=
    fun t : ℝ =>
      (1 / δ ^ 2) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
  have hδ_pos : 0 < δ :=
    hε_pos
  have hg_integrable : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    exact
      Real.binetSecondFormula_kernel_majorant_integrableOn.const_mul
        (1 / δ ^ 2)
  refine ⟨ε, hε_pos, g, hg_integrable, ?_⟩
  intro z hz t ht
  have hδ_le_re : δ ≤ z.re :=
    hε_subset z hz
  exact
    Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
      hδ_pos hδ_le_re ht

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  exact
    Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
      hw_re_pos

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, sufficient for differentiating the Binet remainder under
the integral sign near `w` in the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_locally_dominated
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases
    Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
      hw_re_pos with
    ⟨ε, hε_pos, g, hg_int, hg_bound⟩
  refine ⟨ε, hε_pos, g, hg_int, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  exact hg_bound z hz t ht

/-- The arctangent kernel and differentiated Binet kernel have the measurability
and base-point integrability needed for dominated differentiation. -/
theorem Complex.binetSecondFormulaRemainder_integral_data
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (∀ᶠ z in 𝓝 w,
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / z) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  exact
    ⟨Eventually.of_forall
        (fun z =>
          Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable z),
      Complex.binetSecondFormula_arctanKernel_integrable hw_re_pos,
      Complex.binetSecondFormulaDerivativeKernel_aestronglyMeasurable w⟩

/-- Membership in a smaller ball gives the norm inequality needed for a larger
radius measured in the normed-space coordinates. -/
theorem Complex.norm_sub_lt_of_mem_ball_of_le_radius
    {w z : ℂ}
    {ε η : ℝ}
    (hε_le_η : ε ≤ η)
    (hz : z ∈ Metric.ball w ε) :
    ‖z - w‖ < η := by
  have hdist : dist z w < ε :=
    Metric.mem_ball.mp hz
  have hnorm : ‖z - w‖ < ε := by
    have hdist_eq : dist z w = ‖z - w‖ :=
      dist_eq_norm z w
    exact
      Eq.subst
        (motive := fun x : ℝ => x < ε)
        hdist_eq
        hdist
  exact lt_of_lt_of_le hnorm hε_le_η

/-- The a.e. arctangent-kernel derivative statement on a ball restricts to
any smaller ball. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_on_smaller_ball
    {w : ℂ}
    {ε η : ℝ}
    (hε_le_η : ε ≤ η)
    (hkernel :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w η →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z) :
    ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
      ∀ z : ℂ,
        z ∈ Metric.ball w ε →
          HasDerivAt
            (fun u : ℂ =>
              Complex.arctan ((t : ℂ) / u) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
            (Complex.binetSecondFormulaDerivativeKernel t z) z :=
  hkernel.mono
    (fun t ht z hz =>
      ht z
        (Metric.mem_ball.mpr
          (by
            have hnorm : ‖z - w‖ < η :=
              Complex.norm_sub_lt_of_mem_ball_of_le_radius
                hε_le_η hz
            have hdist_eq : dist z w = ‖z - w‖ :=
              dist_eq_norm z w
            exact
              Eq.subst
                (motive := fun x : ℝ => x < η)
                hdist_eq.symm
                hnorm)))

/-- The a.e. derivative-kernel majorant on a ball restricts to any smaller
ball. -/
theorem Complex.binetSecondFormula_derivativeKernel_bound_on_smaller_ball
    {w : ℂ}
    {ε η : ℝ}
    {g : ℝ → ℝ}
    (hε_le_η : ε ≤ η)
    (hbound :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w η →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
      ∀ z : ℂ,
        z ∈ Metric.ball w ε →
          ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t :=
  hbound.mono
    (fun t ht z hz =>
      ht z
        (Metric.mem_ball.mpr
          (by
            have hnorm : ‖z - w‖ < η :=
              Complex.norm_sub_lt_of_mem_ball_of_le_radius
                hε_le_η hz
            have hdist_eq : dist z w = ‖z - w‖ :=
              dist_eq_norm z w
            exact
              Eq.subst
                (motive := fun x : ℝ => x < η)
                hdist_eq.symm
                hnorm)))

/-- The Binet arctangent kernel is a.e.-strongly measurable on the positive
half-line. -/
theorem Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable
    (z : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / z) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / z) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
    fun_prop
  exact hmeas.aestronglyMeasurable

/-- The differentiated Binet kernel is a.e.-strongly measurable on the positive
half-line. -/
theorem Complex.binetSecondFormulaDerivativeKernel_aestronglyMeasurable
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w) := by
    fun_prop [Complex.binetSecondFormulaDerivativeKernel]
  exact hmeas.aestronglyMeasurable

/-- Early local small-argument estimate for the Binet arctangent argument. -/
theorem Complex.binetSecondFormula_small_interval_argument_norm_le_half_for_integrability
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) := by
  exact
    Complex.binetSecondFormula_small_interval_argument_norm_le_half
      hw_re_pos ht

/-- Early small-interval pointwise domination for the Binet kernel. -/
theorem Complex.binetSecondFormula_kernel_norm_le_on_small_interval_for_integrability
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  have hkernel :
      ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Complex.binetSecondFormula_kernel_norm_le_on_small_interval
      hw_re_pos ht
  have hrewrite :
      (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
        (2 / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_eq
      t ‖w‖
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤ x)
      hrewrite
      hkernel

/-- The Binet kernel is integrable on the lower split interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioc (0 : ℝ) (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_kernel_norm_le_on_small_interval_for_integrability
          hw_re_pos ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Tail pointwise domination for the Binet kernel on the open right
half-plane after the split at `‖w‖ / 2`. -/
theorem Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            C *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases
      Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound
        hw_re_pos with
    ⟨C, hC_nonneg, harctan_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_pos : 0 < t :=
    lt_of_le_of_lt
      (div_nonneg (norm_nonneg w) zero_le_two)
      ht_tail
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht_pos
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t :=
    harctan_bound t ht_tail
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      exact congrArg (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x) hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact (mul_div_assoc C t (Real.exp ((2 : ℝ) * Real.pi * t) - 1)).symm

/-- The Binet kernel is integrable on the upper split interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨c, hc_nonneg, htail_bound⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- The Binet arctangent kernel is integrable at each point of the open right
half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_integrable
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Integrable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hsmall : IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  have hK_integrable : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    hunion ▸ hsmall.union htail
  exact hK_integrable

/-- Uniform-a.e. differentiability of the Binet arctangent kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
          ∀ z : ℂ,
            z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  refine ⟨ε, hε_pos, ?_⟩
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  intro z hz
  have hnorm : ‖z - w‖ < ε := by
    exact
      Complex.norm_sub_lt_of_mem_ball_of_le_radius
        (le_refl ε) hz
  exact
    Complex.binetSecondFormula_arctanKernel_hasDerivAt
      ht (hε_subset z hnorm)

/-- Uniform-a.e. domination of the differentiated Binet kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases
      Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
        hw_re_pos with
    ⟨ε, hε_pos, g, hg_int, hg_bound⟩
  refine ⟨ε, hε_pos, g, hg_int, ?_⟩
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  intro z hz
  have hnorm : ‖z - w‖ < ε := by
    exact
      Complex.norm_sub_lt_of_mem_ball_of_le_radius
        (le_refl ε) hz
  exact hg_bound z hnorm t ht

/-- Dominated-differentiation transport for the Binet remainder once the
measurability and base-point integrability data have been supplied. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
    {w : ℂ}
    {ε : ℝ}
    (hε_pos : 0 < ε)
    (hF_meas :
      ∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF_int :
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    {g : ℝ → ℝ}
    (hg_int :
      Integrable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hbound :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t)
    (hdiff :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  let μ : Measure ℝ := Measure.restrict volume (Set.Ioi (0 : ℝ))
  let F : ℂ → ℝ → ℂ :=
    fun z t =>
      Complex.arctan ((t : ℂ) / z) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let F' : ℂ → ℝ → ℂ :=
    fun z t => Complex.binetSecondFormulaDerivativeKernel t z
  have hmain :
      Integrable (F' w) μ ∧
        HasDerivAt
          (fun z : ℂ => ∫ t, F z t ∂μ)
          (∫ t, F' w t ∂μ) w := by
    exact
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := μ)
        (x₀ := w)
        (F := F)
        (F' := F')
        (bound := g)
        hε_pos
        (by exact hF_meas)
        (by exact hF_int)
        (by exact hF'_meas)
        (by exact hbound)
        (by exact hg_int)
        (by exact hdiff)
  have hscaled :
      HasDerivAt
        (fun z : ℂ => 2 * ∫ t, F z t ∂μ)
        (2 * ∫ t, F' w t ∂μ) w :=
    hmain.2.const_mul 2
  exact hscaled

/-- Integral derivative transport for the Binet second-formula remainder from
the pointwise arctangent-kernel derivative and its local integrable majorant. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
    {w : ℂ}
    (hdata :
      (∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
        Integrable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
        AEStronglyMeasurable
          (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hkernel :
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z)
    (hdominated :
      ∃ ε : ℝ,
        0 < ε ∧
        ∃ g : ℝ → ℝ,
          IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ∀ z : ℂ,
                z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  rcases hdata with ⟨hF_meas, hF_int, hF'_meas⟩
  rcases hkernel with ⟨ε₁, hε₁_pos, hkernel_bound⟩
  rcases hdominated with ⟨ε₂, hε₂_pos, g, hg_int, hdominated_bound⟩
  let ε : ℝ := min ε₁ ε₂
  have hε_pos : 0 < ε :=
    lt_min hε₁_pos hε₂_pos
  have hε_le_ε₁ : ε ≤ ε₁ :=
    min_le_left ε₁ ε₂
  have hε_le_ε₂ : ε ≤ ε₂ :=
    min_le_right ε₁ ε₂
  have hdiff :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z :=
    Complex.binetSecondFormula_arctanKernel_derivative_on_smaller_ball
      hε_le_ε₁ hkernel_bound
  have hbound :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t :=
    Complex.binetSecondFormula_derivativeKernel_bound_on_smaller_ball
      hε_le_ε₂ hdominated_bound
  exact
    Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
      hε_pos hF_meas hF_int hF'_meas hg_int hbound hdiff

/-- Differentiation under the integral sign for the Binet second-formula
remainder. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
      (Complex.binetSecondFormulaRemainder_integral_data
        hw_re_pos)
      (Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
        hw_re_pos)
      (Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
        hw_re_pos)

/-- The logarithmic derivative of the principal-log Gamma side on the open
right half-plane, stated as the exact special-function derivative owner fact
needed for Binet's differentiated formula. -/
theorem Complex.logGamma_hasDerivAt_openRightHalfPlane_from_Gamma_derivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => Complex.log (Complex.Gamma z))
      (deriv Complex.Gamma w / Complex.Gamma w) w := by
  have hnot_pole : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hw_eq
    have hre_nonpos : w.re ≤ 0 := by
      have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hw_eq
      exact hre.symm ▸ le_of_eq (by rfl)
    exact not_lt_of_ge hre_nonpos hw_re_pos
  have hgamma_deriv :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hnot_pole).hasDerivAt
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero hnot_pole
  exact hgamma_deriv.clog hgamma_ne

/-- Points in the open right half-plane lie in the principal-log slit plane. -/
theorem Complex.mem_slitPlane_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ∈ Complex.slitPlane := by
  have hnot_nonpos : ¬ w ≤ 0 := by
    intro hw_nonpos
    have hw_im_zero : w.im = 0 :=
      (Complex.nonpos_iff.mp hw_nonpos).2
    have hw_re_nonpos : w.re ≤ 0 :=
      (Complex.nonpos_iff.mp hw_nonpos).1
    exact not_lt_of_ge hw_re_nonpos hw_re_pos
  exact (Complex.mem_slitPlane_iff_not_le_zero).2 hnot_nonpos

/-- The explicit Binet main term is complex-differentiable on the open right
half-plane. -/
theorem Complex.binetLogGammaMainTerm_differentiableAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    DifferentiableAt ℂ Complex.binetLogGammaMainTerm w := by
  have hlog_diff :
      DifferentiableAt ℂ (fun z : ℂ => Complex.log z) w :=
    differentiableAt_id.clog
      (Complex.mem_slitPlane_of_re_pos hw_re_pos)
  have hmain :
      DifferentiableAt ℂ
        (fun z : ℂ =>
          (z - (1 / 2 : ℂ)) * Complex.log z - z +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) w :=
    (((differentiableAt_id.const_sub (1 / 2 : ℂ)).mul hlog_diff).sub
      differentiableAt_id).const_add _
  exact hmain

/-- Explicit derivative of the Binet logarithmic main term on the open right
half-plane. -/
theorem Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetLogGammaMainTerm
      (Complex.log w - (1 / (2 * w))) w := by
  have hw_ne_zero : w ≠ 0 :=
    Complex.ne_zero_of_re_pos hw_re_pos
  have hlog :
      HasDerivAt (fun z : ℂ => Complex.log z) (1 / w) w :=
    (hasDerivAt_id' w).clog
      (Complex.mem_slitPlane_of_re_pos hw_re_pos)
  have hfactor :
      HasDerivAt (fun z : ℂ => z - (1 / 2 : ℂ)) 1 w :=
    (hasDerivAt_id' w).sub_const (1 / 2 : ℂ)
  have hprod :
      HasDerivAt
        (fun z : ℂ => (z - (1 / 2 : ℂ)) * Complex.log z)
        (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) w :=
    hfactor.mul hlog
  have hmain :
      HasDerivAt
        (fun z : ℂ =>
          (z - (1 / 2 : ℂ)) * Complex.log z - z +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
        ((1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0) w :=
    ((hprod.sub (hasDerivAt_id' w)).const_add
      ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2))
  have hderiv :
      (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 =
        Complex.log w - (1 / (2 * w)) := by
    field_simp [hw_ne_zero]
    ring
  exact hmain

/-- The derivative value of the Binet logarithmic main term on the open right
half-plane. -/
theorem Complex.deriv_binetLogGammaMainTerm_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.binetLogGammaMainTerm w =
      Complex.log w - (1 / (2 * w)) := by
  exact
    (Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
      hw_re_pos).deriv

/-- Derivative of the analytic Binet logarithm branch on the open right
half-plane. -/
theorem Complex.binetLogGammaBranch_hasDerivAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetLogGammaBranch
      ((Complex.log w - (1 / (2 * w))) +
        Complex.binetSecondFormulaRemainderDerivative w)
      w := by
  have hmain :
      HasDerivAt
        Complex.binetLogGammaMainTerm
        (Complex.log w - (1 / (2 * w))) w :=
    Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
      hw_re_pos
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  exact hmain.add hremainder

/-- The standard Binet log-derivative identity with the differentiated
arctangent-kernel integral written out.  This is the remaining special-function
input after the local derivative transport and Binet main-term derivative have
both been proved from local calculus. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  let D : ℂ :=
    (Complex.log w - (1 / (2 * w))) +
      Complex.binetSecondFormulaRemainderDerivative w
  have hbranch_deriv :
      HasDerivAt Complex.binetLogGammaBranch D w := by
    dsimp [D]
    exact
      Complex.binetLogGammaBranch_hasDerivAt_openRightHalfPlane
        hw_re_pos
  have hexp_branch_deriv :
      HasDerivAt
        (fun z : ℂ => Complex.exp (Complex.binetLogGammaBranch z))
        (Complex.exp (Complex.binetLogGammaBranch w) * D) w :=
    hbranch_deriv.cexp
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  have heq_eventually :
      (fun z : ℂ => Complex.exp (Complex.binetLogGammaBranch z)) =ᶠ[𝓝 w]
        Complex.Gamma := by
    have hball :
        ∀ᶠ z : ℂ in 𝓝 w, ‖z - w‖ < ε :=
      (Metric.eventually_nhds_iff_ball.2
        ⟨ε, hε_pos, fun z hz => hz⟩)
    exact hball.mono
      (fun z hz =>
        Complex.Gamma_binetSecondFormula_branchExponential
          (hε_subset z hz))
  have hgamma_from_branch :
      HasDerivAt Complex.Gamma
        (Complex.exp (Complex.binetLogGammaBranch w) * D) w :=
    hexp_branch_deriv.congr_of_eventuallyEq heq_eventually
  have hnot_pole : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hw_eq
    have hre_nonpos : w.re ≤ 0 := by
      have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hw_eq
      exact hre.symm ▸ le_of_eq (by rfl)
    exact not_lt_of_ge hre_nonpos hw_re_pos
  have hgamma_deriv :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hnot_pole).hasDerivAt
  have hderiv_eq :
      Complex.exp (Complex.binetLogGammaBranch w) * D =
        deriv Complex.Gamma w :=
    hgamma_from_branch.unique hgamma_deriv
  have hbranch_exp :
      Complex.exp (Complex.binetLogGammaBranch w) =
        Complex.Gamma w :=
    Complex.Gamma_binetSecondFormula_branchExponential hw_re_pos
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero hnot_pole
  have hD_eq :
      D =
        deriv Complex.Gamma w / Complex.Gamma w := by
    calc
      D = (Complex.Gamma w)⁻¹ * (Complex.Gamma w * D) := by
        exact (inv_mul_cancel_left₀ hgamma_ne).symm
      _ = (Complex.Gamma w)⁻¹ * deriv Complex.Gamma w := by
        exact congrArg (fun u : ℂ => (Complex.Gamma w)⁻¹ * u)
          (Eq.trans hbranch_exp.symm hderiv_eq)
      _ = deriv Complex.Gamma w / Complex.Gamma w := by
        exact (div_eq_mul_inv _ _).symm
  exact hD_eq.symm

/-- The standard Binet log-derivative identity with the differentiated
arctangent-kernel integral written out. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_owner
      hw_re_pos

/-- The standard Binet log-derivative identity in the local remainder-derivative
normalization used by this file. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        Complex.binetSecondFormulaRemainderDerivative w := by
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
      hw_re_pos

/-- The differentiated Binet identity at the logarithmic-derivative level:
the Gamma logarithmic derivative minus the derivative of the explicit main
term is the derivative of the Binet remainder. -/
theorem Complex.Gamma_logDerivative_sub_binetMainTerm_derivative_eq_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.Gamma w / Complex.Gamma w -
        deriv Complex.binetLogGammaMainTerm w =
      Complex.binetSecondFormulaRemainderDerivative w := by
  have hmain :
      deriv Complex.binetLogGammaMainTerm w =
        Complex.log w - (1 / (2 * w)) :=
    Complex.deriv_binetLogGammaMainTerm_openRightHalfPlane hw_re_pos
  have hlogderiv :
      deriv Complex.Gamma w / Complex.Gamma w =
        (Complex.log w - (1 / (2 * w))) +
          Complex.binetSecondFormulaRemainderDerivative w :=
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_remainderDerivative
      hw_re_pos
  calc
    deriv Complex.Gamma w / Complex.Gamma w -
        deriv Complex.binetLogGammaMainTerm w =
        ((Complex.log w - (1 / (2 * w))) +
          Complex.binetSecondFormulaRemainderDerivative w) -
            (Complex.log w - (1 / (2 * w))) := by
          have hA :
              deriv Complex.Gamma w / Complex.Gamma w =
                (Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w :=
            hlogderiv
          have hB :
              deriv Complex.binetLogGammaMainTerm w =
                Complex.log w - (1 / (2 * w)) :=
            hmain
          calc
            deriv Complex.Gamma w / Complex.Gamma w -
                deriv Complex.binetLogGammaMainTerm w =
                (((Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w) -
                    deriv Complex.binetLogGammaMainTerm w) := by
              exact congrArg
                (fun x : ℂ => x - deriv Complex.binetLogGammaMainTerm w) hA
            _ =
                ((Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w) -
                    (Complex.log w - (1 / (2 * w))) := by
              exact congrArg
                (fun x : ℂ =>
                  ((Complex.log w - (1 / (2 * w))) +
                    Complex.binetSecondFormulaRemainderDerivative w) - x) hB
    _ = Complex.binetSecondFormulaRemainderDerivative w := by
          abel

/-- The derivative of the principal-log Gamma side minus the explicit Binet
main term, reduced to the logarithmic-derivative Binet identity. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_from_logDerivative_identity
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  have hlog :
      HasDerivAt
        (fun z : ℂ => Complex.log (Complex.Gamma z))
        (deriv Complex.Gamma w / Complex.Gamma w) w :=
    Complex.logGamma_hasDerivAt_openRightHalfPlane_from_Gamma_derivative
      hw_re_pos
  have hmain :
      HasDerivAt
        Complex.binetLogGammaMainTerm
        (deriv Complex.binetLogGammaMainTerm w) w :=
    (Complex.binetLogGammaMainTerm_differentiableAt_openRightHalfPlane
      hw_re_pos).hasDerivAt
  have hsub :=
    hlog.sub hmain
  have hderiv_eq :
      deriv Complex.Gamma w / Complex.Gamma w -
          deriv Complex.binetLogGammaMainTerm w =
        Complex.binetSecondFormulaRemainderDerivative w :=
    Complex.Gamma_logDerivative_sub_binetMainTerm_derivative_eq_remainderDerivative
      hw_re_pos
  exact hderiv_eq ▸ hsub

/-- The special-function derivative identity behind Binet's second
formula: the logarithmic derivative of Gamma minus the derivative of the
explicit Binet main term is the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_from_logDerivative_identity
      hw_re_pos

/-- The logarithmic Gamma side and explicit Binet main term have the
derivative prescribed by the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
      hw_re_pos

/-- The logarithmic Gamma side, after subtracting the explicit Binet main
term, has derivative equal to the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
      hw_re_pos

/-- Differentiating the arctangent-kernel integral under the integral sign
gives the same logarithmic derivative as the Gamma side after subtracting the
explicit Binet main term. -/
theorem Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  have hlog_main :
      HasDerivAt
        (fun z : ℂ =>
          Complex.log (Complex.Gamma z) -
            Complex.binetLogGammaMainTerm z)
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
      hw_re_pos
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  exact hlog_main.sub hremainder

/-- A complex function with zero derivative on the open right half-plane is
constant there.  This is the convex-domain mean-value theorem specialized to
the right half-plane. -/
theorem Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
    {F : ℂ → ℂ}
    (hderiv : ∀ {z : ℂ}, 0 < z.re → HasDerivAt F 0 z) :
    ∀ {z w : ℂ}, 0 < z.re → 0 < w.re → F z = F w := by
  intro z w hz hw
  let S : Set ℂ := {u : ℂ | 0 < u.re}
  have hconv : Convex ℝ S := by
    exact convex_halfSpace_re_gt (r := 0)
  have hopen : IsOpen S := by
    exact
      (isOpen_lt continuous_const Complex.continuous_re :
        IsOpen {u : ℂ | (0 : ℝ) < u.re})
  have hdiff : DifferentiableOn ℂ F S := by
    intro u hu
    exact (hderiv hu).differentiableAt.differentiableWithinAt
  have hzero :
      ∀ u ∈ S, fderivWithin ℂ F S u = 0 := by
    intro u hu
    have hunique : UniqueDiffWithinAt ℂ S u :=
      hopen.uniqueDiffWithinAt hu
    exact
      (hderiv hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin hunique
  exact hconv.is_const_of_fderivWithin_eq_zero hdiff hzero hz hw

/-- The two sides of Binet's second formula have the same complex derivative
on the open right half-plane.

This is the analytic continuation/differentiation root: after differentiating
the arctangent-kernel integral under the integral sign, the derivative agrees
with the logarithmic derivative of `Gamma` minus the derivative of the explicit
main term. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  exact
    Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
      hw_re_pos

/-- A holomorphic Binet difference with zero derivative on the open right
half-plane is determined there by its positive-real values. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
    (hreal :
      ∀ {x : ℝ},
        0 < x →
          Complex.log (Complex.Gamma (x : ℂ)) =
            Complex.binetLogGammaMainTerm (x : ℂ) +
              Complex.binetSecondFormulaRemainder (x : ℂ))
    (hderiv :
      ∀ {w : ℂ},
        0 < w.re →
          HasDerivAt
            (fun z : ℂ =>
              Complex.log (Complex.Gamma z) -
                (Complex.binetLogGammaMainTerm z +
                  Complex.binetSecondFormulaRemainder z))
            0 w) :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  intro w hw
  let F : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.log (Complex.Gamma z) -
        (Complex.binetLogGammaMainTerm z +
          Complex.binetSecondFormulaRemainder z)
  have hbase_re : 0 < (w.re : ℂ).re := by
    exact hw
  have hconstant : F (w.re : ℂ) = F w :=
    Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
      (F := F)
      (fun hz => hderiv hz)
      hbase_re hw
  have hbase_zero : F (w.re : ℂ) = 0 := by
    dsimp [F]
    exact sub_eq_zero.mpr (hreal hw)
  have hw_zero : F w = 0 := by
    exact Eq.trans hconstant.symm hbase_zero
  exact sub_eq_zero.mp hw_zero

/-- The open right half-plane is connected to the positive real axis by
paths along which the principal-log Binet difference has zero derivative.

This consumes the real-axis normalization and the zero-derivative identity to
propagate Binet's formula through the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
      (fun hx =>
        Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
          hx)
      (fun hw_re_pos =>
        Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
          hw_re_pos)

/-- The classical second Binet integral representation, with the principal
logarithm normalization used by `Complex.binetLogGammaMainTerm` and the
literal arctangent-kernel remainder used in this package. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_principalLog :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative

/-- Binet's logarithmic identity follows from the classical second Binet
integral representation on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_principalLog

/-- Binet's second logarithmic formula on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation

/-- The literal arctangent-kernel Binet formula is an open-right-half-plane
statement.  On the boundary `w = i y`, the kernel crosses the principal
arctangent branch point at `t = y`, so this theorem records the large-radius
form for the existing pointwise integral only on `0 < w.re`. -/
theorem Complex.Gamma_binetSecondFormula_large_openRightHalfPlane :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro w hw_re_pos _hR
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane
      w hw_re_pos

/-- Large-radius Binet formula for the existing principal-arctangent integral.
The hypothesis is open half-plane because the current remainder is the
pointwise kernel integral, not a boundary-value object on the imaginary axis. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_large_openRightHalfPlane

/-- Closed-sector continuation of Binet's second logarithmic formula after a
large-radius cutoff for the literal open-half-plane arctangent remainder. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation

/-- Binet's second logarithmic formula for Gamma in the open right half-plane,
away from the origin and after a fixed large-radius cutoff. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation

end

end LFunctions
end Boundary
