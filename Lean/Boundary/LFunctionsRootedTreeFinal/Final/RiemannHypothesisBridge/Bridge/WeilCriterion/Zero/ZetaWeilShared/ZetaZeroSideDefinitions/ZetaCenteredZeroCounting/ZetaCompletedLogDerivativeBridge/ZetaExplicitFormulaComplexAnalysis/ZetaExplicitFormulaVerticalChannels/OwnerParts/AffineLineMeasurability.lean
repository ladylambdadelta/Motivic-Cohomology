import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels

/-!
# Measurability of affine vertical-line test-transform factors

This file owns the shared continuity and strong-measurability facts for the
fixed affine vertical lines used by prime, inverse-Gamma, and pole kernels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Continuity of the right affine line. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- Continuity of the shifted right affine line. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaRightCenteredAffineLine F t) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- Continuity of the left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- Continuity of the shifted left affine line. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) :=
  continuous_const.add
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- The right affine line has positive real part, hence avoids `0`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_ne_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t ≠ 0 := by
  intro hzero
  have hre :
      (zetaCompletedExplicitFormulaRightAffineLine F t).re = (0 : ℂ).re :=
    congrArg Complex.re hzero
  have hzero_re : (0 : ℂ).re = (0 : ℝ) :=
    Complex.zero_re
  have hright_re :
      (zetaCompletedExplicitFormulaRightAffineLine F t).re = F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_re F t
  have hc_zero : F.c = 0 :=
    hright_re.symm.trans (hre.trans hzero_re)
  exact (ne_of_gt F.c_pos) hc_zero

/-- The right affine line has real part strictly greater than one, hence avoids
`1`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_ne_one
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t ≠ 1 := by
  intro hone
  have hre :
      (zetaCompletedExplicitFormulaRightAffineLine F t).re = (1 : ℂ).re :=
    congrArg Complex.re hone
  have hone_re : (1 : ℂ).re = (1 : ℝ) :=
    Complex.one_re
  have hright_re :
      (zetaCompletedExplicitFormulaRightAffineLine F t).re = F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_re F t
  have hc_one : F.c = 1 :=
    hright_re.symm.trans (hre.trans hone_re)
  exact (ne_of_gt F.c_gt_one) hc_one

/-- The right affine line lies in the absolute-convergence half-plane. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_one_lt_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (1 : ℝ) < (zetaCompletedExplicitFormulaRightAffineLine F t).re :=
  Eq.subst
    (motive := fun x : ℝ => (1 : ℝ) < x)
    (zetaCompletedExplicitFormulaRightAffineLine_re F t).symm
    F.c_gt_one

/-- The completed zeta factor is nonzero on the right affine line. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_completedRiemannZeta_ne_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaRightAffineLine F t) ≠ 0 := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hs_re : (1 : ℝ) < s.re :=
    zetaCompletedExplicitFormulaRightAffineLine_one_lt_re F t
  have hs0 : s ≠ 0 :=
    zetaCompletedExplicitFormulaRightAffineLine_ne_zero F t
  have hΓ : Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs_re)
  have hζ : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs_re
  have hfactor :
      completedRiemannZeta s = riemannZeta s * Gammaℝ s :=
    zetaCompletedExplicitFormula_completed_factorization hs0 hΓ
  exact fun hzero =>
    (mul_ne_zero hζ hΓ) (hfactor.symm.trans hzero)

/-- The completed-zeta negative logarithmic derivative is continuous on the
right affine line.  The right line is in `Re s > 1`, hence avoids the completed
zeta zeros and the points `0` and `1`. -/
theorem zetaCompletedExplicitFormulaCompletedNegLogDeriv_rightAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous
      (fun t : ℝ =>
        completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F t)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  exact
    (differentiableAt_completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine_ne_zero F t)
      (zetaCompletedExplicitFormulaRightAffineLine_ne_one F t)
      (zetaCompletedExplicitFormulaRightAffineLine_completedRiemannZeta_ne_zero
        F t)).continuousAt.comp
        ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).continuousAt)

/-- The completed-zeta negative logarithmic derivative is strongly measurable
on the right affine line. -/
theorem zetaCompletedExplicitFormulaCompletedNegLogDeriv_rightAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCompletedNegLogDeriv_rightAffineLine_continuous
    F).aestronglyMeasurable

/-- Strong measurability of the reflected completed-log-derivative factor used
by the left prime reflection. -/
theorem zetaCompletedExplicitFormulaCompletedNegLogDeriv_reflectedRightAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        - completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
      (volume : Measure ℝ) := by
  have hright :
      Continuous
        (fun t : ℝ =>
          completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)) :=
    zetaCompletedExplicitFormulaCompletedNegLogDeriv_rightAffineLine_continuous
      F
  have hreflected :
      Continuous
        (fun t : ℝ =>
          completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))) :=
    hright.comp continuous_id.neg
  exact hreflected.neg.aestronglyMeasurable

/-- The completed zeta factor is nonzero on the left affine line, since that
line lies in the negative real half-plane. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_completedRiemannZeta_ne_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaLeftAffineLine F t) ≠ 0 :=
  completedRiemannZeta_ne_zero_of_re_lt_zero
    (zetaCompletedExplicitFormulaLeftAffineLine F t)
    (zetaCompletedExplicitFormulaLeftAffineLine_re_lt_zero F t)

/-- The punctured left affine line, excluding only central height, is a
zero-excised strip carrier for the completed-zeta logarithmic derivative. -/
def zetaCompletedExplicitFormulaLeftAffineLinePuncturedZeroExcisedStrip
    (F : ExplicitFormulaContourFamily) :
    CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c) where
  carrier :=
    {z : ℂ | ∃ t : ℝ,
      t ≠ 0 ∧ z = zetaCompletedExplicitFormulaLeftAffineLine F t}
  in_strip := by
    intro z hz
    match hz with
    | ⟨t, _ht, hzt⟩ =>
        have hzre : z.re = 1 - F.c :=
          (congrArg Complex.re hzt).trans
            (zetaCompletedExplicitFormulaLeftAffineLine_re F t)
        exact ⟨le_of_eq hzre.symm, le_of_eq hzre⟩
  ne_zero := by
    intro z hz
    match hz with
    | ⟨t, _ht, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_ne_zero F t)
  ne_one := by
    intro z hz
    match hz with
    | ⟨t, _ht, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => w ≠ 1)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_ne_one F t)
  zeta_ne_zero := by
    intro z hz
    match hz with
    | ⟨t, _ht, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_completedRiemannZeta_ne_zero
              F t)
  gamma_ne_zero := by
    intro z hz
    match hz with
    | ⟨t, ht, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => Gammaℝ w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_ne_zero_height
              F ht)

/-- A noncentral point of the left affine line belongs to its punctured
zero-excised strip carrier. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_mem_puncturedZeroExcisedStrip
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    zetaCompletedExplicitFormulaLeftAffineLine F t ∈
      (zetaCompletedExplicitFormulaLeftAffineLinePuncturedZeroExcisedStrip
        F).carrier :=
  ⟨t, ht, rfl⟩

/-- The whole left affine line is zero-excised for a vertically regular contour
family.  This packages the owner contour regularity into the carrier needed by
whole-line logarithmic-derivative estimates. -/
def zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
    (F : ExplicitFormulaVerticallyRegularContourFamily) :
    CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) where
  carrier :=
    {z : ℂ | ∃ t : ℝ,
      z = zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t}
  in_strip := by
    intro z hz
    match hz with
    | ⟨t, hzt⟩ =>
        have hzre : z.re = 1 - F.toContourFamily.c :=
          (congrArg Complex.re hzt).trans
            (zetaCompletedExplicitFormulaLeftAffineLine_re
              F.toContourFamily t)
        exact ⟨le_of_eq hzre.symm, le_of_eq hzre⟩
  ne_zero := by
    intro z hz
    match hz with
    | ⟨t, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_ne_zero
              F.toContourFamily t)
  ne_one := by
    intro z hz
    match hz with
    | ⟨t, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => w ≠ 1)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_ne_one
              F.toContourFamily t)
  zeta_ne_zero := by
    intro z hz
    match hz with
    | ⟨t, hzt⟩ =>
        exact
          Eq.subst
            (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_completedRiemannZeta_ne_zero
              F.toContourFamily t)
  gamma_ne_zero := by
    intro z hz
    match hz with
    | ⟨t, hzt⟩ =>
        have hregular :
            zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
              F.toContourFamily :=
          zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
            F
        exact
          Eq.subst
            (motive := fun w : ℂ => Gammaℝ w ≠ 0)
            hzt.symm
            (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
              F.toContourFamily hregular t)

/-- Every point of the left affine line belongs to the whole-line
zero-excised carrier attached to a vertically regular contour family. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular
    (F : ExplicitFormulaVerticallyRegularContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
      (zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
        F).carrier :=
  ⟨t, rfl⟩

/-- The Gamma factor is nonzero on the right affine line. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos
    (lt_trans zero_lt_one
      (zetaCompletedExplicitFormulaRightAffineLine_one_lt_re F t))

/-- The right affine line misses the nonpositive-even `Gammaℝ` singular
locus. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_ne_Gammaℝ_zero_locus
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaRightAffineLine F t ≠
        -(2 * (n : ℂ)) := by
  intro n hline
  have hzero :
      Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) = 0 :=
    Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hline⟩
  exact
    (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t)
      hzero

/-- Deligne's `Gammaℝ` is differentiable at every point of the right affine
line. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_differentiableAt
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    DifferentiableAt ℂ Gammaℝ
      (zetaCompletedExplicitFormulaRightAffineLine F t) :=
  Gammaℝ_differentiableAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaRightAffineLine_ne_Gammaℝ_zero_locus F t)

/-- Exact `Gammaℝ` derivative formula on the right affine line. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_hasDerivAt
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    HasDerivAt Gammaℝ
      (((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaRightAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
                (1 / 2 : ℂ)))
      (zetaCompletedExplicitFormulaRightAffineLine F t) :=
  Gammaℝ_hasDerivAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaRightAffineLine_ne_Gammaℝ_zero_locus F t)

/-- The derivative of `Gammaℝ` on the right affine line is the explicit
Deligne-product derivative. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_deriv_Gammaℝ_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) =
      ((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaRightAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
                (1 / 2 : ℂ)) :=
  (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_hasDerivAt F t).deriv

/-- The `Gammaℝ` logarithmic derivative on the right affine line is the
elementary `π` contribution plus one half of the ordinary Gamma logarithmic
derivative at half the affine argument. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma
            (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
          (1 / 2 : ℂ)) /
          Complex.Gamma
            (zetaCompletedExplicitFormulaRightAffineLine F t / 2) :=
  Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
    (zetaCompletedExplicitFormulaRightAffineLine_ne_Gammaℝ_zero_locus F t)
    (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t)

/-- On the right affine line, the inverse-Gamma completion correction is the
negative logarithmic derivative of `Gammaℝ`. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaRightAffineLine F t) =
      -deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) :=
  inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_differentiableAt F t)
    (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t)

/-- The prime logarithmic derivative is continuous on the right affine line. -/
theorem zetaCompletedExplicitFormulaPrimeLogDerivative_rightAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  exact
    (explicitFormulaPrimeLogDerivative_continuousAt_of_regular
      (zetaCompletedExplicitFormulaRightAffineLine F t)
      (zetaCompletedExplicitFormulaRightAffineLine_ne_zero F t)
      (zetaCompletedExplicitFormulaRightAffineLine_ne_one F t)
      (zetaCompletedExplicitFormulaRightAffineLine_completedRiemannZeta_ne_zero F t)
      (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t)).comp
        ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).continuousAt)

/-- Under the parameter-level Gamma-regularity condition, the prime
logarithmic derivative is continuous on the left affine line. -/
theorem zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_continuous_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Continuous
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  exact
    (explicitFormulaPrimeLogDerivative_continuousAt_of_regular
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_ne_zero F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_ne_one F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_completedRiemannZeta_ne_zero F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
        F hregular t)).comp
        ((zetaCompletedExplicitFormulaLeftAffineLine_continuous F).continuousAt)

/-- Under the parameter-level Gamma-regularity condition, the left affine
prime logarithmic derivative is strongly measurable. -/
theorem zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_aestronglyMeasurable_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_continuous_of_gammaRegular
    F hregular).aestronglyMeasurable

/-- On the right affine line, the von Mangoldt Dirichlet-series factor is the
prime logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    L ↗Λ (zetaCompletedExplicitFormulaRightAffineLine F t) =
      explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t) :=
  (explicitFormulaPrimeLogDerivative_eq_vonMangoldt_LSeries_of_one_lt_re
    (zetaCompletedExplicitFormulaRightAffineLine F t)
    (zetaCompletedExplicitFormulaRightAffineLine_one_lt_re F t)).symm

/-- Strong measurability of the right von Mangoldt Dirichlet-series factor. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ => L ↗Λ (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) := by
  have hlog :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    (zetaCompletedExplicitFormulaPrimeLogDerivative_rightAffineLine_continuous
      F).aestronglyMeasurable
  exact hlog.congr
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
          F t).symm))

/-- The absolute-series bound for the right von Mangoldt factor on the fixed
line `Re s = F.c`. -/
noncomputable def zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound
    (F : ExplicitFormulaContourFamily) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (↗Λ) (F.c : ℂ) n‖

/-- The right von Mangoldt factor bound is nonnegative. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg
    (F : ExplicitFormulaContourFamily) :
    0 ≤ zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F :=
  tsum_nonneg
    (fun n : ℕ => norm_nonneg (LSeries.term (↗Λ) (F.c : ℂ) n))

/-- The absolute von Mangoldt L-series at the real point `F.c` is summable. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_summable
    (F : ExplicitFormulaContourFamily) :
    Summable (fun n : ℕ => ‖LSeries.term (↗Λ) (F.c : ℂ) n‖) :=
  (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (F.c : ℂ))
    (Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      (Complex.ofReal_re F.c).symm
      F.c_gt_one)).norm

/-- The norm of each von Mangoldt L-series term is constant on the vertical
line `Re s = F.c`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_norm_eq
    (F : ExplicitFormulaContourFamily) (t : ℝ) (n : ℕ) :
    ‖LSeries.term (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) n‖ =
      ‖LSeries.term (↗Λ) (F.c : ℂ) n‖ := by
  have hre :
      (zetaCompletedExplicitFormulaRightAffineLine F t).re = (F.c : ℂ).re :=
    (zetaCompletedExplicitFormulaRightAffineLine_re F t).trans
      (Complex.ofReal_re F.c).symm
  calc
    ‖LSeries.term (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) n‖ =
        if n = 0 then 0
        else ‖(↗Λ : ℕ → ℂ) n‖ /
          (n : ℝ) ^
            (zetaCompletedExplicitFormulaRightAffineLine F t).re := by
      exact LSeries.norm_term_eq (↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t) n
    _ =
        if n = 0 then 0
        else ‖(↗Λ : ℕ → ℂ) n‖ / (n : ℝ) ^ (F.c : ℂ).re := by
      exact congrArg
        (fun x : ℝ =>
          if n = 0 then 0 else ‖(↗Λ : ℕ → ℂ) n‖ / (n : ℝ) ^ x)
        hre
    _ = ‖LSeries.term (↗Λ) (F.c : ℂ) n‖ := by
      exact (LSeries.norm_term_eq (↗Λ) (F.c : ℂ) n).symm

/-- Absolute summability of the right affine von Mangoldt terms on every
vertical line `Re s = F.c`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    Summable
      (fun n : ℕ =>
        ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n‖) := by
  have hbase :
      Summable
        (fun n : ℕ => ‖LSeries.term (↗Λ) (F.c : ℂ) n‖) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_summable F
  have hterms :
      (fun n : ℕ =>
        ‖LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n‖) =
      (fun n : ℕ => ‖LSeries.term (↗Λ) (F.c : ℂ) n‖) := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_norm_eq
        F t n
  exact
    Eq.subst
      (motive := fun φ : ℕ → ℝ => Summable φ)
      hterms.symm
      hbase

/-- Complex summability of the right affine von Mangoldt terms. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_complex_summable
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    Summable
      (fun n : ℕ =>
        LSeries.term (↗Λ)
          (zetaCompletedExplicitFormulaRightAffineLine F t) n) := by
  exact
    Summable.of_norm
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_summable
        F t)

/-- The right von Mangoldt Dirichlet-series factor is uniformly bounded on the
fixed right affine line. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_norm_le_bound
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    ‖L ↗Λ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hsumm :
      Summable (fun n : ℕ => ‖LSeries.term (↗Λ) s n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := s)
      (zetaCompletedExplicitFormulaRightAffineLine_one_lt_re F t)).norm
  have hnorm :
      ‖L ↗Λ s‖ ≤ ∑' n : ℕ, ‖LSeries.term (↗Λ) s n‖ :=
    norm_tsum_le_tsum_norm hsumm
  have hterms :
      (fun n : ℕ => ‖LSeries.term (↗Λ) s n‖) =
        fun n : ℕ => ‖LSeries.term (↗Λ) (F.c : ℂ) n‖ := by
    funext n
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_term_norm_eq
        F t n
  have hsum :
      (∑' n : ℕ, ‖LSeries.term (↗Λ) s n‖) =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F :=
    congrArg
      (fun φ : ℕ → ℝ => ∑' n : ℕ, φ n)
      hterms
  exact hnorm.trans_eq hsum

/-- The inverse-Gamma logarithmic-derivative factor is continuous on the right
affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_continuous
    (F : ExplicitFormulaContourFamily) :
    Continuous
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F t)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hgammaAnalytic :
      AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hderiv :
      ContinuousAt (fun z : ℂ => deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z) s :=
    analyticAt_deriv_continuousAt hgammaAnalytic
  have hgammaInv :
      ContinuousAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hgamma :
      Gammaℝ s ≠ 0 :=
    zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t
  have hgammaInv_ne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero hgamma
  have hquot :
      ContinuousAt
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z / (Gammaℝ z)⁻¹)
        s :=
    hderiv.div hgammaInv hgammaInv_ne
  have hdef :
      (fun z : ℂ => inverseGammaCompletionLogDeriv z) =
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z / (Gammaℝ z)⁻¹) := by
    funext z
    exact inverseGammaCompletionLogDeriv_eq z
  exact
    (Eq.subst
      (motive := fun φ : ℂ → ℂ => ContinuousAt φ s)
      hdef.symm
      hquot).comp
        ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).continuousAt)

/-- Strong measurability of the inverse-Gamma logarithmic-derivative factor on
the right affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_continuous
    F).aestronglyMeasurable

/-- Under the parameter-level Gamma-regularity condition, Deligne's `Gammaℝ`
is differentiable at every point of the left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_differentiableAt_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    DifferentiableAt ℂ Gammaℝ
      (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  Gammaℝ_differentiableAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
      F hregular t)

/-- Away from central height, Deligne's `Gammaℝ` is differentiable at the
left affine line point. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_differentiableAt_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    DifferentiableAt ℂ Gammaℝ
      (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  Gammaℝ_differentiableAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
      F ht)

/-- Exact `Gammaℝ` derivative formula on a gamma-regular left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_hasDerivAt_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    HasDerivAt Gammaℝ
      (((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
                (1 / 2 : ℂ)))
      (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  Gammaℝ_hasDerivAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
      F hregular t)

/-- Away from central height, the exact `Gammaℝ` derivative formula holds on
the left affine line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_hasDerivAt_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt Gammaℝ
      (((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
                (1 / 2 : ℂ)))
      (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  Gammaℝ_hasDerivAt_of_ne_zero_locus
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
      F ht)

/-- The derivative of `Gammaℝ` on a gamma-regular left affine line is the
explicit Deligne-product derivative. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_deriv_Gammaℝ_eq_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      ((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
                (1 / 2 : ℂ)) :=
  (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_hasDerivAt_of_gammaRegular
    F hregular t).deriv

/-- Away from central height, the derivative of `Gammaℝ` on the left affine
line is the explicit Deligne-product derivative. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_deriv_Gammaℝ_eq_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      ((Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) *
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) +
        (Real.pi : ℂ) ^
          (-(zetaCompletedExplicitFormulaLeftAffineLine F t) / 2) *
            (deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
                (1 / 2 : ℂ)) :=
  (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_hasDerivAt_of_ne_zero_height
    F ht).deriv

/-- On a gamma-regular left affine line, the `Gammaℝ` logarithmic derivative is
the explicit elementary `π` contribution plus one half of the ordinary Gamma
logarithmic derivative at half the affine argument. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
          (1 / 2 : ℂ)) /
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) :=
  Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_gammaRegular
      F hregular t)
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
      F hregular t)

/-- Away from central height, the `Gammaℝ` logarithmic derivative on the left
affine line is the explicit elementary `π` contribution plus one half of the
ordinary Gamma logarithmic derivative at half the affine argument. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
          (1 / 2 : ℂ)) /
          Complex.Gamma
            (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) :=
  Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
    (zetaCompletedExplicitFormulaLeftAffineLine_ne_Gammaℝ_zero_locus_of_ne_zero_height
      F ht)
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_ne_zero_height
      F ht)

/-- Under the parameter-level Gamma-regularity condition, the inverse-Gamma
completion correction is the negative logarithmic derivative of `Gammaℝ` on
the left affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      -deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_differentiableAt_of_gammaRegular
      F hregular t)
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
      F hregular t)

/-- Away from central height, the inverse-Gamma completion correction is the
negative logarithmic derivative of `Gammaℝ` on the left affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_ne_zero_height
    (F : ExplicitFormulaContourFamily) {t : ℝ} (ht : t ≠ 0) :
    inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      -deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
        Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
  inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_differentiableAt_of_ne_zero_height
      F ht)
    (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_ne_zero_height
      F ht)

/-- Under the parameter-level Gamma-regularity condition, the inverse-Gamma
logarithmic-derivative factor is continuous on the left affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_continuous_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Continuous
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)) := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  have hgammaAnalytic :
      AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hderiv :
      ContinuousAt (fun z : ℂ => deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z) s :=
    analyticAt_deriv_continuousAt hgammaAnalytic
  have hgammaInv :
      ContinuousAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hgamma :
      Gammaℝ s ≠ 0 :=
    zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
      F hregular t
  have hgammaInv_ne : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero hgamma
  have hquot :
      ContinuousAt
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z / (Gammaℝ z)⁻¹)
        s :=
    hderiv.div hgammaInv hgammaInv_ne
  have hdef :
      (fun z : ℂ => inverseGammaCompletionLogDeriv z) =
        (fun z : ℂ =>
          deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z / (Gammaℝ z)⁻¹) := by
    funext z
    exact inverseGammaCompletionLogDeriv_eq z
  exact
    (Eq.subst
      (motive := fun φ : ℂ → ℂ => ContinuousAt φ s)
      hdef.symm
      hquot).comp
        ((zetaCompletedExplicitFormulaLeftAffineLine_continuous F).continuousAt)

/-- Under the parameter-level Gamma-regularity condition, the inverse-Gamma
logarithmic-derivative factor on the left affine line is strongly measurable. -/
theorem zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_aestronglyMeasurable_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_continuous_of_gammaRegular
    F hregular).aestronglyMeasurable

/-- The test transform is continuous on the right shifted affine line. -/
theorem zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z) :=
    continuous_iff_continuousAt.2
      (fun z => (h.phi_control.differentiableAt z).continuousAt)
  exact hPhi.comp
    (zetaCompletedExplicitFormulaRightCenteredAffineLine_continuous F)

/-- The test transform is continuous on the left shifted affine line. -/
theorem zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_continuous
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z) :=
    continuous_iff_continuousAt.2
      (fun z => (h.phi_control.differentiableAt z).continuousAt)
  exact hPhi.comp
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine_continuous F)

/-- Strong measurability of the right shifted affine-line test transform. -/
theorem zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_continuous
    f F h).aestronglyMeasurable

/-- Strong measurability of the left shifted affine-line test transform. -/
theorem zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_continuous
    f F h).aestronglyMeasurable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
