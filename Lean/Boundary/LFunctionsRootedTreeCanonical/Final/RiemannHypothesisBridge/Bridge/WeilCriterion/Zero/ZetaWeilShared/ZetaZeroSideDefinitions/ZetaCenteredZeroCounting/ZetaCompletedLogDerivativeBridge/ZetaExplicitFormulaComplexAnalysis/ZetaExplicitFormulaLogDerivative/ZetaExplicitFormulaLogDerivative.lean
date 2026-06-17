import Boundary.LFunctions.ZetaCompletedLogDerivativeCore
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Boundary explicit-formula log derivative channel API

This file owns the pointwise channel decomposition of the completed negative
logarithmic derivative into its prime, archimedean, and correction packet
components.  Vertical contour files realize this packet decomposition by
integration; they do not own the pointwise normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The prime-side logarithmic derivative contribution. -/
def explicitFormulaPrimeLogDerivative (s : ℂ) : ℂ :=
  completedZetaNegLogDeriv s - inverseGammaCompletionLogDeriv s

/-- The pole correction logarithmic derivative contribution. -/
def explicitFormulaCorrectionLogDerivative (s : ℂ) : ℂ :=
  - 1 / s - 1 / (s - 1)

/-- The archimedean logarithmic derivative contribution. -/
def explicitFormulaArchimedeanLogDerivative (s : ℂ) : ℂ :=
  inverseGammaCompletionLogDeriv s -
    explicitFormulaCorrectionLogDerivative s

/-- The completed explicit-formula channel packet: prime plus archimedean plus correction. -/
def explicitFormulaCompletedLogDerivative (s : ℂ) : ℂ :=
  explicitFormulaPrimeLogDerivative s +
    explicitFormulaArchimedeanLogDerivative s +
    explicitFormulaCorrectionLogDerivative s

/-- On the regular domain, the totalized prime channel is the negative logarithmic
derivative of the ordinary zeta factor. -/
theorem explicitFormulaPrimeLogDerivative_eq_neg_logDeriv_of_regular
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    explicitFormulaPrimeLogDerivative s = - logDeriv riemannZeta s := by
  have hbridge :
      zetaSideNegLogDeriv s =
        completedZetaNegLogDeriv s -
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ :=
    zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
      hs0 hs1 hΛ hΓ
  have hside :
      zetaSideNegLogDeriv s = riemannZetaNegLogDeriv s :=
    zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv hs0 hΛ hΓ
  have hriemann :
      riemannZetaNegLogDeriv s = - logDeriv riemannZeta s := by
    unfold riemannZetaNegLogDeriv
    calc
      -deriv riemannZeta s / riemannZeta s =
          -(deriv riemannZeta s / riemannZeta s) := by
        exact neg_div (riemannZeta s) (deriv riemannZeta s)
      _ = -logDeriv riemannZeta s := by
        exact Eq.symm <| congrArg Neg.neg (logDeriv_apply (f := riemannZeta) (x := s))
  unfold explicitFormulaPrimeLogDerivative
  calc
    completedZetaNegLogDeriv s - inverseGammaCompletionLogDeriv s =
        completedZetaNegLogDeriv s -
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
      exact congrArg
        (fun x : ℂ => completedZetaNegLogDeriv s - x)
        (inverseGammaCompletionLogDeriv_eq s)
    _ = zetaSideNegLogDeriv s := hbridge.symm
    _ = riemannZetaNegLogDeriv s := hside
    _ = -logDeriv riemannZeta s := hriemann

/-- The archimedean channel is normalized so that adding the pole-correction channel gives
the inverse-Gamma correction from the completed-zeta factorization. -/
theorem explicitFormulaArchimedeanLogDerivative_eq_inverseGammaCorrection_sub_poleCorrection
    (s : ℂ) :
    explicitFormulaArchimedeanLogDerivative s =
      inverseGammaCompletionLogDeriv s -
        explicitFormulaCorrectionLogDerivative s := by
  rfl

/-- The correction channel is the negative logarithmic derivative of the two pole faces. -/
theorem explicitFormulaCorrectionLogDerivative_eq_poleCorrection
    (s : ℂ) :
    explicitFormulaCorrectionLogDerivative s = - 1 / s - 1 / (s - 1) := by
  rfl

/-- A complex analytic germ has continuous complex derivative at the center. -/
theorem analyticAt_deriv_continuousAt
    {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) :
    ContinuousAt (fun z : ℂ => deriv g z) s := by
  exact hg.deriv.continuousAt

/-- The ordinary Riemann zeta function is analytic away from its pole at `1`. -/
theorem riemannZeta_analyticAt_of_ne_one
    (s : ℂ) (hs1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  exact analyticAt_riemannZeta hs1

/-- Continuity of the ordinary zeta derivative at a regular point. -/
theorem deriv_riemannZeta_continuousAt_of_analyticAt
    (s : ℂ) (hs1 : s ≠ 1) :
    ContinuousAt (fun z : ℂ => deriv riemannZeta z) s := by
  exact analyticAt_deriv_continuousAt
    (riemannZeta_analyticAt_of_ne_one s hs1)

/-- Continuity of the ordinary zeta derivative at a regular point. -/
theorem deriv_riemannZeta_continuousAt_of_regular
    (s : ℂ) (hs1 : s ≠ 1) :
    ContinuousAt (fun z : ℂ => deriv riemannZeta z) s := by
  exact deriv_riemannZeta_continuousAt_of_analyticAt s hs1

/-- Continuity of the Gamma logarithmic derivative term at a regular point. -/
theorem log_Gammaℝ_analyticAt_of_ne_zero
    (s : ℂ) (hΓ : Gammaℝ s ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (Gammaℝ z)) s := by
  exact (Complex.analyticAt_log hΓ).comp (Complex.analyticAt_Gammaℝ s)

/-- Continuity of the Gamma logarithmic derivative term at a regular point. -/
theorem deriv_log_Gammaℝ_continuousAt_of_analyticAt
    (s : ℂ) (hΓ : Gammaℝ s ≠ 0) :
    ContinuousAt (fun z : ℂ => deriv (fun w : ℂ => Complex.log (Gammaℝ w)) z) s := by
  exact analyticAt_deriv_continuousAt
    (log_Gammaℝ_analyticAt_of_ne_zero s hΓ)

/-- Continuity of the Gamma logarithmic derivative term at a regular point. -/
theorem deriv_log_Gammaℝ_continuousAt_of_regular
    (s : ℂ) (hΓ : Gammaℝ s ≠ 0) :
    ContinuousAt (fun z : ℂ => deriv (fun w : ℂ => Complex.log (Gammaℝ w)) z) s := by
  exact deriv_log_Gammaℝ_continuousAt_of_analyticAt s hΓ

/-- Regular completed-zeta points give nonvanishing of the ordinary zeta denominator in the
prime channel. -/
theorem riemannZeta_ne_zero_of_completed_regular
    (s : ℂ) (hs0 : s ≠ 0) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_completed_ne_zero hs0 hΛ hΓ

/-- Prime-channel pointwise continuity on the regular completed-zeta domain.

Analytically this is continuity of `-ζ'/ζ` at points where the zeta denominator is regular;
the completed nonvanishing package supplies the corresponding ordinary zeta nonvanishing
through the normalization bridge. -/
theorem explicitFormulaPrimeLogDerivative_continuousAt_of_regular
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    ContinuousAt explicitFormulaPrimeLogDerivative s := by
  have hζ : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_completed_regular s hs0 hΛ hΓ
  have hregular :
      explicitFormulaPrimeLogDerivative s = - logDeriv riemannZeta s :=
    explicitFormulaPrimeLogDerivative_eq_neg_logDeriv_of_regular
      s hs0 hs1 hΛ hΓ
  have hordinary :
      ContinuousAt (fun z : ℂ => - logDeriv riemannZeta z) s := by
    unfold logDeriv
    exact
      ((deriv_riemannZeta_continuousAt_of_regular s hs1).div
        ((differentiableAt_riemannZeta hs1).continuousAt)
        hζ).neg
  have htotalized :
      ContinuousAt explicitFormulaPrimeLogDerivative s :=
    hordinary.congr_of_eventuallyEq ?_
  exact htotalized
  filter_upwards
    [eventually_ne_nhds hs0,
      eventually_ne_nhds hs1,
      (differentiableAt_completedZeta hs0 hs1).continuousAt.eventually_ne hΛ,
      (Complex.analyticAt_Gammaℝ s).continuousAt.eventually_ne hΓ]
    with z hz0 hz1 hΛz hΓz
  exact
    explicitFormulaPrimeLogDerivative_eq_neg_logDeriv_of_regular
      z hz0 hz1 hΛz hΓz

/-- Archimedean-channel pointwise continuity on the regular completed-zeta domain.

This is the local regularity of the Gamma/digamma logarithmic derivative under the completed
normalization exclusions. -/
theorem explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    ContinuousAt explicitFormulaArchimedeanLogDerivative s := by
  have hΓinv : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero hΓ
  have hgammaAnalytic :
      AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.analyticAt s
  have hderiv :
      ContinuousAt (fun z : ℂ => deriv (fun w : ℂ => (Gammaℝ w)⁻¹) z) s :=
    analyticAt_deriv_continuousAt hgammaAnalytic
  have hgammaInv :
      ContinuousAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hcorrection :
      ContinuousAt explicitFormulaCorrectionLogDerivative s := by
    unfold explicitFormulaCorrectionLogDerivative
    have hsub : s - 1 ≠ 0 :=
      sub_ne_zero.mpr hs1
    exact
      (continuousAt_const.neg.div continuousAt_id hs0).sub
        (continuousAt_const.div
          (continuousAt_id.sub continuousAt_const) hsub)
  unfold explicitFormulaArchimedeanLogDerivative
  exact
    (hderiv.div hgammaInv hΓinv).sub hcorrection

/-- The zeta-side logarithmic derivative is the prime channel on the completed regular
domain. -/
theorem zetaSideNegLogDeriv_eq_explicitFormulaPrimeLogDerivative_of_regular
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    zetaSideNegLogDeriv s = explicitFormulaPrimeLogDerivative s := by
  have hbridge :
      zetaSideNegLogDeriv s =
        completedZetaNegLogDeriv s -
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ :=
    zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
      hs0 hs1 hΛ hΓ
  unfold explicitFormulaPrimeLogDerivative
  calc
    zetaSideNegLogDeriv s =
        completedZetaNegLogDeriv s -
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := hbridge
    _ = completedZetaNegLogDeriv s - inverseGammaCompletionLogDeriv s := by
      exact congrArg
        (fun x : ℂ => completedZetaNegLogDeriv s - x)
        (inverseGammaCompletionLogDeriv_eq s).symm

/-- The inverse-Gamma correction in the completed normalization is the archimedean channel
plus the pole-face correction in the explicit-formula normalization.

This is the remaining normalization bridge between the Mathlib completed-zeta
factorization and the channel packet used by the explicit formula. -/
theorem inverseGammaCorrection_eq_archimedean_add_poleCorrection
    (s : ℂ) :
    deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ =
      explicitFormulaArchimedeanLogDerivative s +
        explicitFormulaCorrectionLogDerivative s := by
  rw [← inverseGammaCompletionLogDeriv_eq s]
  unfold explicitFormulaArchimedeanLogDerivative
  exact sub_add_cancel
    (inverseGammaCompletionLogDeriv s)
    (explicitFormulaCorrectionLogDerivative s)

/-- Completed negative logarithmic derivative decomposition on the regular completed-zeta
domain. -/
theorem completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_of_regular
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedZetaNegLogDeriv s = explicitFormulaCompletedLogDerivative s := by
  have hzetaSide :
      zetaSideNegLogDeriv s =
      explicitFormulaPrimeLogDerivative s :=
    zetaSideNegLogDeriv_eq_explicitFormulaPrimeLogDerivative_of_regular
      s hs0 hs1 hΛ hΓ
  have hcompleted :
      completedZetaNegLogDeriv s =
        zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ :=
    sub_eq_iff_eq_add.mp
      (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
        hs0 hs1 hΛ hΓ).symm
  have hgamma :
      deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ =
        explicitFormulaArchimedeanLogDerivative s +
          explicitFormulaCorrectionLogDerivative s :=
    inverseGammaCorrection_eq_archimedean_add_poleCorrection s
  unfold explicitFormulaCompletedLogDerivative
  calc
    completedZetaNegLogDeriv s =
        zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := hcompleted
    _ = explicitFormulaPrimeLogDerivative s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
      exact congrArg
        (fun z : ℂ => z +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹)
        hzetaSide
    _ = explicitFormulaPrimeLogDerivative s +
          (explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s) := by
      exact congrArg (fun z : ℂ => explicitFormulaPrimeLogDerivative s + z) hgamma
    _ = explicitFormulaPrimeLogDerivative s +
          explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s := by
      exact (add_assoc
        (explicitFormulaPrimeLogDerivative s)
        (explicitFormulaArchimedeanLogDerivative s)
        (explicitFormulaCorrectionLogDerivative s)).symm

/-- Totalized extension of the regular completed log-derivative channel decomposition.

The channel definitions are normalized so the completed packet is exact at all totalized
points; the ordinary Euler-product interpretation is retained separately on the regular
domain. -/
theorem completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_of_totalizedExtension
    (s : ℂ) :
    completedZetaNegLogDeriv s = explicitFormulaCompletedLogDerivative s := by
  let Z : ℂ := completedZetaNegLogDeriv s
  let G : ℂ := inverseGammaCompletionLogDeriv s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  unfold explicitFormulaCompletedLogDerivative
  unfold explicitFormulaPrimeLogDerivative
  unfold explicitFormulaArchimedeanLogDerivative
  change Z = (Z - G) + (G - C) + C
  calc
    Z = (Z - G) + G := by
      exact (sub_add_cancel Z G).symm
    _ = (Z - G) + ((G - C) + C) := by
      exact congrArg (fun x : ℂ => (Z - G) + x) (sub_add_cancel G C).symm
    _ = (Z - G) + (G - C) + C := by
      exact (add_assoc (Z - G) (G - C) C).symm

/-- Completed negative logarithmic derivative decomposition into the prime, archimedean, and
pole-correction channel packet.

Proof chain: differentiate the completed-zeta normalization, use the ordinary zeta
logarithmic derivative for the Euler-product channel, identify the Gamma-factor derivative
with the archimedean channel, and differentiate the two pole-face corrections. -/
theorem completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_ownerCompletedLogDerivativeDecomposition
    (s : ℂ) :
    completedZetaNegLogDeriv s = explicitFormulaCompletedLogDerivative s := by
  exact completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_of_totalizedExtension s


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
