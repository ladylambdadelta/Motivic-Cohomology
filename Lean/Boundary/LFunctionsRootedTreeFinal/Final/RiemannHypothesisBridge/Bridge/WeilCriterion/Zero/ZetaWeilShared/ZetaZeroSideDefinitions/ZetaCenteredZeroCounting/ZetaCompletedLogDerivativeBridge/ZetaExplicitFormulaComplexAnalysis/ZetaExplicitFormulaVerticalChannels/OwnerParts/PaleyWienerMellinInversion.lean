import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Paley-Wiener Mellin inversion normalization

This file owns the vertical-channel wrapper around the repository's canonical
Mellin/Fourier inversion convention.  It is intentionally placed above the
prime right Paley-Wiener sampling leaf so the `2π` normalization is settled
before any von Mangoldt arithmetic is applied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open scoped FourierTransform

namespace ZetaAdmissibleFunction

/-- The centered vertical line of `Φ_f` is the reflected Fourier transform of
the horizontally twisted time kernel. -/
theorem zetaCompletedExplicitFormulaPhi_verticalLine_eq_fourierIntegral_expTwist
    (f : ZetaAdmissibleFunction) (σ y : ℝ) :
    zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I) =
      𝓕 (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) (-y) := by
  have hphi :
      zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I) =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          (σ + 2 * π * y * I) := by
    exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f)
      (σ + 2 * π * y * I)
  have hline :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          (σ + 2 * π * y * I) =
        𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) (-y) :=
    Boundary.zetaLaplaceTransform_verticalLine_eq_fourierIntegral_expTwist
      f.toZetaTestFunction' σ y
  exact hphi.trans hline

/-- Fourier inversion for the vertical line of `Φ_f`, with the reflected
frequency convention introduced by the explicit-formula vertical parameter.

The output is the horizontally twisted time-side boundary value.  Later prime
sampling lemmas specialize `a = log n` and cancel this horizontal twist against
the natural character normalization. -/
theorem zetaCompletedExplicitFormulaPhi_verticalLine_inverseFourier_sample
    (f : ZetaAdmissibleFunction) (σ a : ℝ)
    (htwist_integrable :
      Integrable
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t))
    (hfourier_integrable :
      Integrable
        (𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)))
    (hcontinuous :
      ContinuousAt
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)
        a) :
    𝓕⁻ (fun y : ℝ =>
        zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I)) (-a) =
      Complex.exp ((σ : ℂ) * (a : ℂ)) *
        zetaCompletedTimeBoundaryValue f a := by
  let g : ℝ → ℂ :=
    fun t : ℝ =>
      Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t
  have hline :
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I)) =
        fun y : ℝ => 𝓕 g (-y) := by
    funext y
    exact zetaCompletedExplicitFormulaPhi_verticalLine_eq_fourierIntegral_expTwist
      f σ y
  have hinv :
      𝓕⁻ (fun y : ℝ => 𝓕 g (-y)) (-a) = g a :=
    Boundary.boundary_real_fourier_inversion_reflected
      (f := g) (x := a)
      htwist_integrable hfourier_integrable hcontinuous
  have htime :
      g a =
        Complex.exp ((σ : ℂ) * (a : ℂ)) *
          zetaCompletedTimeBoundaryValue f a := by
    exact congrArg
      (fun z : ℂ => Complex.exp ((σ : ℂ) * (a : ℂ)) * z)
      (zetaCompletedTimeBoundaryValue_eq_apply f a).symm
  calc
    𝓕⁻ (fun y : ℝ =>
        zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I)) (-a) =
        𝓕⁻ (fun y : ℝ => 𝓕 g (-y)) (-a) := by
      exact congrArg (fun H : ℝ → ℂ => 𝓕⁻ H (-a)) hline
    _ = g a :=
      hinv
    _ =
        Complex.exp ((σ : ℂ) * (a : ℂ)) *
          zetaCompletedTimeBoundaryValue f a :=
      htime

/-- Direct vertical-line Mellin inverse integrand in the repository convention.

The real variable here is the actual vertical coordinate `t` on the line
`σ + t I`; no Fourier `2π` reparametrization has been made yet. -/
noncomputable def zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (-(σ + t * I)) • F (σ + t * I)

/-- The unnormalized direct vertical-line Mellin integral. -/
noncomputable def zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ,
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand σ F x t

/-- The normalized direct vertical-line Mellin inverse.

This is intentionally the same normalization as mathlib's `mellinInv`: the
factor `1 / (2π)` belongs here, not in the downstream prime scalar algebra. -/
noncomputable def zetaCompletedExplicitFormulaDirectVerticalMellinInv
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * π)) •
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x

/-- The direct vertical-line integrand unfolds to the integrand used by
mathlib's `mellinInv`. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand_eq
    (σ : ℝ) (F : ℂ → ℂ) (x t : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand σ F x t =
      (x : ℂ) ^ (-(σ + t * I)) • F (σ + t * I) := by
  rfl

/-- The direct vertical-line integral unfolds to the raw integral in
mathlib's `mellinInv`. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x =
      ∫ t : ℝ, (x : ℂ) ^ (-(σ + t * I)) • F (σ + t * I) := by
  rfl

/-- The direct vertical-line inverse is definitionally mathlib's `mellinInv`
in the complex-valued convention. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_mellinInv
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x =
      mellinInv σ F x := by
  rfl

/-- The direct vertical-line inverse is the raw vertical integral with the
Mellin normalization factor `1/(2π)`.

Downstream project-convention Fourier statements should use this theorem
before comparing raw `t`-line integrals with time-side samples. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_prefactor_integral
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x =
      (1 / (2 * π)) •
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x := by
  rfl

/-- The raw vertical-line Mellin integral is `2π` times the normalized direct
Mellin inverse. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_mellinInv
    (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x =
      (2 * π : ℝ) •
        zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x := by
  let I : ℂ :=
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x
  let A : ℂ :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x
  have hdef : A = (1 / (2 * π : ℝ)) • I :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_prefactor_integral
      σ F x
  have htwo : (2 * π : ℝ) ≠ 0 := by
    exact mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hscalar :
      (2 * π : ℝ) * (1 / (2 * π : ℝ)) = 1 :=
    mul_inv_cancel₀ htwo
  calc
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral σ F x =
        I := by
      rfl
    _ = (1 : ℝ) • I := by
      exact (one_smul ℝ I).symm
    _ = ((2 * π : ℝ) * (1 / (2 * π : ℝ))) • I := by
      exact congrArg (fun r : ℝ => r • I) hscalar.symm
    _ = (2 * π : ℝ) • ((1 / (2 * π : ℝ)) • I) := by
      exact (smul_smul (2 * π : ℝ) (1 / (2 * π : ℝ)) I).symm
    _ = (2 * π : ℝ) • A := by
      exact congrArg (fun z : ℂ => (2 * π : ℝ) • z) hdef.symm
    _ =
        (2 * π : ℝ) •
          zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x := by
      rfl

/-- Owner wrapper for the repository Mellin inverse/Fourier bridge in the
complex-valued convention used by the explicit-formula vertical channel.

This theorem is only the canonical `y`-parameter normalization
`σ + 2π y I`.  The direct vertical-line `t`-parameter theorem must still
perform the change of variables `t = 2π y` explicitly before it is consumed by
the prime sampling leaf. -/
theorem zetaCompletedExplicitFormula_mellinInv_eq_fourierIntegralInv_ownerPaleyWiener
    (σ : ℝ) (F : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ F x =
      (x : ℂ) ^ (-σ : ℂ) •
        𝓕⁻ (fun y : ℝ => F (σ + 2 * π * y * I)) (-Real.log x) := by
  exact
    boundary_mellinInv_eq_fourierIntegralInv
      (σ := σ) (f := F) (x := x) hx

/-- Direct vertical-line Mellin inverse expressed in the repository inverse
Fourier convention.

The right-hand side still uses the Fourier variable `y` and the line
`σ + 2π y I`; this theorem is the safe normalization bridge before any
downstream conversion from `y` to a raw vertical coordinate is attempted. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_fourierIntegralInv
    (σ : ℝ) (F : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ F x =
      (x : ℂ) ^ (-σ : ℂ) •
        𝓕⁻ (fun y : ℝ => F (σ + 2 * π * y * I)) (-Real.log x) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_mellinInv
        σ F x)
      (zetaCompletedExplicitFormula_mellinInv_eq_fourierIntegralInv_ownerPaleyWiener
        σ F hx)

/-- Positive-real cancellation between the Mellin character and the horizontal
exponential twist.

For `0 < x`, the principal logarithm of `(x : ℂ)` is the real logarithm, so
`x ^ (-σ)` cancels `exp (σ log x)`. -/
theorem zetaCompletedExplicitFormula_cpow_neg_mul_exp_log_cancel_of_pos
    {x σ : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-σ : ℂ) *
      Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) = 1 := by
  have hx_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  have hcpow :
      (x : ℂ) ^ (-σ : ℂ) =
        Complex.exp ((Real.log x : ℂ) * (-σ : ℂ)) := by
    exact Eq.trans
      (Complex.cpow_def_of_ne_zero hx_ne (-σ : ℂ))
      (congrArg (fun z : ℂ => Complex.exp (z * (-σ : ℂ))) hlog)
  have hsum :
      (Real.log x : ℂ) * (-σ : ℂ) +
          (σ : ℂ) * (Real.log x : ℂ) =
        0 := by
    calc
      (Real.log x : ℂ) * (-σ : ℂ) +
          (σ : ℂ) * (Real.log x : ℂ) =
        -((Real.log x : ℂ) * (σ : ℂ)) +
          (σ : ℂ) * (Real.log x : ℂ) := by
          exact congrArg
            (fun z : ℂ => z + (σ : ℂ) * (Real.log x : ℂ))
            (mul_neg (Real.log x : ℂ) (σ : ℂ))
      _ =
        -((Real.log x : ℂ) * (σ : ℂ)) +
          ((Real.log x : ℂ) * (σ : ℂ)) := by
          exact congrArg
            (fun z : ℂ => -((Real.log x : ℂ) * (σ : ℂ)) + z)
            (mul_comm (σ : ℂ) (Real.log x : ℂ))
      _ = 0 := by
          exact neg_add_cancel ((Real.log x : ℂ) * (σ : ℂ))
  calc
    (x : ℂ) ^ (-σ : ℂ) *
        Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) =
      Complex.exp ((Real.log x : ℂ) * (-σ : ℂ)) *
        Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) := by
        exact congrArg
          (fun z : ℂ => z * Complex.exp ((σ : ℂ) * (Real.log x : ℂ)))
          hcpow
    _ =
      Complex.exp
        ((Real.log x : ℂ) * (-σ : ℂ) +
          (σ : ℂ) * (Real.log x : ℂ)) := by
        exact (Complex.exp_add
          ((Real.log x : ℂ) * (-σ : ℂ))
          ((σ : ℂ) * (Real.log x : ℂ))).symm
    _ = Complex.exp 0 := by
        exact congrArg Complex.exp hsum
    _ = 1 := by
        exact Complex.exp_zero

/-- Scalar form of the positive-real Mellin character cancellation. -/
theorem zetaCompletedExplicitFormula_cpow_smul_exp_log_cancel_of_pos
    {x σ : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ (-σ : ℂ) •
        (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) * z) =
      z := by
  have hscalar :
      (x : ℂ) ^ (-σ : ℂ) *
        Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) = 1 :=
    zetaCompletedExplicitFormula_cpow_neg_mul_exp_log_cancel_of_pos
      (x := x) (σ := σ) hx
  calc
    (x : ℂ) ^ (-σ : ℂ) •
        (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) * z) =
      ((x : ℂ) ^ (-σ : ℂ)) *
        (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) * z) := by
        rfl
    _ =
      (((x : ℂ) ^ (-σ : ℂ)) *
          Complex.exp ((σ : ℂ) * (Real.log x : ℂ))) * z := by
        exact (mul_assoc
          ((x : ℂ) ^ (-σ : ℂ))
          (Complex.exp ((σ : ℂ) * (Real.log x : ℂ))) z).symm
    _ = 1 * z := by
        exact congrArg (fun w : ℂ => w * z) hscalar
    _ = z := by
        exact one_mul z

/-- Direct Mellin inversion of `Φ_f` reduced to the explicit logarithmic
time-side sample, before cancelling the multiplicative character prefactor.

This theorem is the honest analytic bridge behind the Paley-Wiener sampling
leaf.  The remaining normalization step is purely the positive-real identity
between `(x : ℂ) ^ (-σ)` and `exp (σ log x)`. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_cpow_smul_expLog_timeSample
    (f : ZetaAdmissibleFunction) (σ : ℝ) {x : ℝ} (hx : 0 < x)
    (htwist_integrable :
      Integrable
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t))
    (hfourier_integrable :
      Integrable
        (𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)))
    (hcontinuous :
      ContinuousAt
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)
        (Real.log x)) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
        (zetaCompletedExplicitFormulaPhi f) x =
      (x : ℂ) ^ (-σ : ℂ) •
        (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) *
          zetaCompletedTimeBoundaryValue f (Real.log x)) := by
  have hbridge :
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
          (zetaCompletedExplicitFormulaPhi f) x =
        (x : ℂ) ^ (-σ : ℂ) •
          𝓕⁻ (fun y : ℝ =>
            zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I))
            (-Real.log x) :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_fourierIntegralInv
      σ (zetaCompletedExplicitFormulaPhi f) hx
  have hsample :
      𝓕⁻ (fun y : ℝ =>
          zetaCompletedExplicitFormulaPhi f (σ + 2 * π * y * I))
          (-Real.log x) =
        Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) *
          zetaCompletedTimeBoundaryValue f (Real.log x) :=
    zetaCompletedExplicitFormulaPhi_verticalLine_inverseFourier_sample
      f σ (Real.log x)
      htwist_integrable hfourier_integrable hcontinuous
  exact Eq.trans hbridge
    (congrArg
      (fun z : ℂ => (x : ℂ) ^ (-σ : ℂ) • z)
      hsample)

/-- Direct Mellin inversion of `Φ_f` reconstructs the logarithmic time-side
sample after the positive-real Mellin character is cancelled.

The hypotheses are precisely the standard Fourier inversion hypotheses for
the horizontally twisted time kernel. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_timeSample
    (f : ZetaAdmissibleFunction) (σ : ℝ) {x : ℝ} (hx : 0 < x)
    (htwist_integrable :
      Integrable
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t))
    (hfourier_integrable :
      Integrable
        (𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)))
    (hcontinuous :
      ContinuousAt
        (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)
        (Real.log x)) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
        (zetaCompletedExplicitFormulaPhi f) x =
      zetaCompletedTimeBoundaryValue f (Real.log x) := by
  have hraw :
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
          (zetaCompletedExplicitFormulaPhi f) x =
        (x : ℂ) ^ (-σ : ℂ) •
          (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) *
            zetaCompletedTimeBoundaryValue f (Real.log x)) :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_cpow_smul_expLog_timeSample
      f σ hx htwist_integrable hfourier_integrable hcontinuous
  have hcancel :
      (x : ℂ) ^ (-σ : ℂ) •
          (Complex.exp ((σ : ℂ) * (Real.log x : ℂ)) *
            zetaCompletedTimeBoundaryValue f (Real.log x)) =
        zetaCompletedTimeBoundaryValue f (Real.log x) :=
    zetaCompletedExplicitFormula_cpow_smul_exp_log_cancel_of_pos
      (x := x) (σ := σ) hx
      (zetaCompletedTimeBoundaryValue f (Real.log x))
  exact Eq.trans hraw hcancel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
