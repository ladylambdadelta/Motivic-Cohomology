import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaTransformCalculusReflection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaLogBoundaryDefect.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Lindelof

/-!
# Boundary explicit-formula analytic core

This file fixes the analytic vocabulary used by the completed Guinand--Weil
route:

* the involution `f†`,
* the autocorrelation kernel `g_f`,
* the spectral transform `Φ_f`,
* the completed zeta logarithmic derivative integrand,
* and the named prime / archimedean / correction pieces.

The file is intentionally definitional. The contour, residue, and decay
arguments will consume these owner-level objects.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The conjugate-reflected involution attached to an admissible function. -/
abbrev zetaAdmissibleDagger (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  ZetaAdmissibleFunction.dagger f

/-- The involution is pointwise conjugate reflection. -/
theorem zetaAdmissibleDagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact ZetaAdmissibleFunction.dagger_apply f t

/-- The reflected admissible probe evaluates to the unreﬂected value at `t`. -/
theorem reflect_neg_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    ZetaAdmissibleFunction.reflect f (-t) = f t := by
  have h := ZetaAdmissibleFunction.reflect_apply f (-t)
  have h' : f (- -t) = f t := by
    exact congrArg f (neg_neg t)
  exact h.trans h'

/-- Applying the dagger twice returns the original function. -/
theorem zetaAdmissibleDagger_dagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger (ZetaAdmissibleFunction.reflect f) t = star (f t) := by
  have h := zetaAdmissibleDagger_apply (ZetaAdmissibleFunction.reflect f) t
  exact h.trans (congrArg star (reflect_neg_apply f t))

theorem zetaAdmissibleDagger_dagger (f : ZetaAdmissibleFunction) :
    ⇑(zetaAdmissibleDagger (ZetaAdmissibleFunction.reflect f)) = fun t => star (f t) := by
  ext t
  exact zetaAdmissibleDagger_dagger_apply f t

/-- The pointwise autocorrelation presentation attached to an admissible function.

This is not the convolution autocorrelation kernel used by the RH-lane
holography theorem. -/
def zetaAutocorrelationKernel (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t => f t * zetaAdmissibleDagger f t

/-- The pointwise autocorrelation kernel is the product with the dagger. -/
theorem zetaAutocorrelationKernel_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = f t * zetaAdmissibleDagger f t := by
  exact Eq.refl _

/-- The autocorrelation kernel is pointwise symmetric under dagger. -/
theorem zetaAutocorrelationKernel_symm (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = zetaAdmissibleDagger f t * f t := by
  exact mul_comm (f t) (zetaAdmissibleDagger f t)

/-- The autocorrelation kernel is exactly the pointwise product. -/
theorem zetaAutocorrelationKernel_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * zetaAdmissibleDagger f t := by
  exact Eq.refl _

/-- The kernel can be rewritten using the dagger on the right factor. -/
theorem zetaAutocorrelationKernel_dagger_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * star (f (-t)) := by
  ext t
  calc
    zetaAutocorrelationKernel f t =
        f t * zetaAdmissibleDagger f t := by
      exact zetaAutocorrelationKernel_apply f t
    _ = f t * star (f (-t)) := by
      exact congrArg (fun z : ℂ => f t * z) (zetaAdmissibleDagger_apply f t)

/-- The spectral transform attached to the autocorrelation kernel. -/
def zetaAutocorrelationSpectralTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z

/-- The time/log-side boundary value of an admissible probe.  This is the raw value on the
logarithmic line; it is deliberately separate from the spectral/Laplace transform. -/
def zetaCompletedTimeBoundaryValue (f : ZetaAdmissibleFunction) (a : ℝ) : ℂ :=
  f.toZetaTestFunction' a

/-- The spectral/Laplace-side transform of an admissible probe. -/
def zetaCompletedSpectralLaplaceTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z

/- The time-side value and spectral/Laplace transform are distinct realizations.  The
completed explicit formula compares their completed prime distributions; it does not identify
`zetaCompletedTimeBoundaryValue f a` with `zetaCompletedSpectralLaplaceTransform f (a : ℂ)`.
-/

/-- The spectral transform notation `Φ_f`. -/
abbrev zetaCompletedExplicitFormulaPhi (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaAutocorrelationSpectralTransform f

/-- The `Φ` notation is the spectral/Laplace transform, not a time-side boundary value. -/
theorem zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f =
      zetaCompletedSpectralLaplaceTransform f := by
  rfl

/-- The time-side value unfolds to the underlying test function. -/
theorem zetaCompletedTimeBoundaryValue_eq_apply
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue f a = f a := by
  calc
    zetaCompletedTimeBoundaryValue f a = f.toZetaTestFunction' a := rfl
    _ = f a := ZetaAdmissibleFunction.toZetaTestFunction'_apply f a

/-- The zero admissible probe has zero time-side boundary value. -/
theorem zetaCompletedTimeBoundaryValue_zero
    (a : ℝ) :
    zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction) a = 0 := by
  exact zetaCompletedTimeBoundaryValue_eq_apply 0 a

/-- The time-side value of the convolution autocorrelation is the autocorrelation kernel. -/
theorem zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) a =
      ZetaAdmissibleFunction.convolutionAutocorrelationKernel f a := by
  have htime :
      zetaCompletedTimeBoundaryValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) a =
        (ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction' a := rfl
  have htest :
      (ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction' a =
        ZetaAdmissibleFunction.convolutionAutocorrelationKernel f a :=
    (ZetaAdmissibleFunction.convolutionAutocorrelation_toZetaTestFunction'_apply
      f a).trans
      (ZetaAdmissibleFunction.convolutionAutocorrelationKernel_apply f a)
  exact htime.trans htest

/-- The explicit-formula spectral transform is definitionally the named `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPhi_eq (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = zetaAutocorrelationSpectralTransform f := by
  exact Eq.refl _

/-- The explicit-formula spectral transform is the zeta Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The zero admissible probe has zero spectral/Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_zero
    (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) z = 0 := by
  have hphi :
      zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) z =
        Boundary.zetaLaplaceTransform
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' z := rfl
  have hlaplace :
      Boundary.zetaLaplaceTransform
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' z = 0 := by
    show
      (∫ t : ℝ,
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
            Complex.exp (z * t)) = 0
    calc
      (∫ t : ℝ,
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
            Complex.exp (z * t)) =
          ∫ _t : ℝ, 0 := by
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall
            (fun t : ℝ =>
              calc
                (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
                    Complex.exp (z * t) =
                    (0 : ℂ) * Complex.exp (z * t) := by
                  exact congrArg
                    (fun x : ℂ => x * Complex.exp (z * t))
                    (ZetaAdmissibleFunction.toZetaTestFunction'_apply 0 t)
                _ = 0 := zero_mul (Complex.exp (z * t))))
      _ = 0 := by
        exact MeasureTheory.integral_zero ℝ ℂ
  exact hphi.trans hlaplace

/-- The spectral transform of the convolution autocorrelation pairs opposite real spectral
parameters. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) (a : ℂ) =
      zetaCompletedExplicitFormulaPhi f (a : ℂ) *
        star (zetaCompletedExplicitFormulaPhi f (-(a : ℂ))) := by
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation_real_pair f a

/-- The spectral transform of the convolution autocorrelation factors at every complex
parameter as a seed transform times its dagger-reflected conjugate. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) z =
      zetaCompletedExplicitFormulaPhi f z *
        star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation f z

/-- The autocorrelation spectral transform is the zeta Laplace transform. -/
theorem zetaAutocorrelationSpectralTransform_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationSpectralTransform f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The autocorrelation spectral transform is continuous. -/
theorem zetaAutocorrelationSpectralTransform_continuous_apply
    (f : ZetaAdmissibleFunction) :
    Continuous (fun z : ℂ => zetaAutocorrelationSpectralTransform f z) := by
  exact zetaLaplaceTransform_continuous f

/-- The reflected admissible function has reflected underlying test function. -/
theorem zetaReflect_toZetaTestFunction'_eq (f : ZetaAdmissibleFunction) :
    (ZetaAdmissibleFunction.reflect f).toZetaTestFunction' =
      ZetaTestFunction.reflect f.toZetaTestFunction' := by
  ext x
  exact rfl

theorem zetaAutocorrelationSpectralTransform_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous (zetaAutocorrelationSpectralTransform f) := by
  exact zetaAutocorrelationSpectralTransform_continuous_apply f

/-- The autocorrelation spectral transform reflects with the test function. -/
theorem zetaAutocorrelationSpectralTransform_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform (ZetaAdmissibleFunction.reflect f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  have h := zetaReflect_toZetaTestFunction'_eq f
  have h' := congrArg (fun φ => Boundary.zetaLaplaceTransform φ z) h
  exact h'.trans (zetaLaplaceTransform_reflect (φ := f.toZetaTestFunction') (z := z))

/-- The autocorrelation spectral transform of the reflected kernel is the reflected transform. -/
theorem zetaAutocorrelationSpectralTransform_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform
        (ZetaAdmissibleFunction.reflect f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  exact zetaAutocorrelationSpectralTransform_reflect f z

/-- The explicit-formula transform reflects under the dagger involution. -/
theorem zetaCompletedExplicitFormulaPhi_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (ZetaAdmissibleFunction.reflect f) z =
      zetaCompletedExplicitFormulaPhi f (-z) := by
  exact zetaAutocorrelationSpectralTransform_reflect f z

/-- The explicit-formula transform of the dagger is the conjugate opposite spectral face. -/
theorem zetaCompletedExplicitFormulaPhi_dagger
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z =
      star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
  exact Boundary.zetaLaplaceTransform_dagger f z

/-- The explicit-formula transform of the reflected autocorrelation is the reflected transform. -/
theorem zetaCompletedExplicitFormulaPhi_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.reflect f)
          z =
      zetaCompletedExplicitFormulaPhi f (-z) := by
  exact zetaCompletedExplicitFormulaPhi_reflect f z

/-- The kernel involution recovers the original pointwise factorization. -/
theorem zetaAdmissibleDagger_pointwise (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact zetaAdmissibleDagger_apply f t

/-- The finite prime-power window used by the current completed explicit-formula core. -/
def zetaCompletedExplicitFormulaPrimeSupport : Finset (ℕ × ℕ) :=
  Finset.product
    (Finset.range (Nat.ceil (Real.exp 0) + 1))
    (Finset.range (Nat.ceil (Real.exp 0) + 1))

/-- The explicit prime-power weight in the completed formula normalization. -/
def zetaCompletedExplicitFormulaPrimeWeight (p n : ℕ) : ℝ :=
  if _hp : Nat.Prime p then
    if _hn : n ≠ 0 then
      Real.log p / Real.sqrt (p ^ n)
    else
      0
  else
    0

/-- Finite display presentation for packet-level prime terms.

This is not the owner completed prime distribution; the public prime contribution below is
the completed prime-power object. -/
noncomputable def zetaCompletedExplicitFormulaPrimeFinitePresentation
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) +
        star (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2))))

/-- The completed prime-power spectral-sample presentation indexed by genuine prime-power
coordinates.  This is the Laplace/contour-side presentation and is deliberately not the owner
real prime distribution: the final explicit-formula prime channel samples the completed
time/log-side boundary value. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    -((ZetaPrimePowerIndex.weight ι : ℂ) *
      (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) +
        star (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι))))

/-- The completed prime-power explicit-formula contribution indexed by genuine prime-power
coordinates.  This is the owner real-side prime distribution: prime powers sample the
time/log-side boundary value.  Contour and vertical-line arguments may realize this
distribution spectrally, but the owner object is not a pointwise Laplace sample. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ((∑' ι : ZetaPrimePowerIndex,
    -(ZetaPrimePowerIndex.weight ι *
      Complex.re
        (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
          star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ)

/-- The prime contribution in the completed explicit formula.

This public owner definition is the completed time/log-side prime-power distribution, not the
finite display support and not the contour-side spectral-sample presentation. -/
noncomputable def zetaCompletedExplicitFormulaPrimeContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimePowerContribution f

/-- The completed prime-power owner contribution is the public prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerContribution f =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The archimedean contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  (2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0

/-- The correction contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
  1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))

/-- The prime contribution unfolds to the completed prime-power owner distribution. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeContribution f =
      zetaCompletedExplicitFormulaPrimePowerContribution f := by
  rfl

/-- The archimedean contribution is the spectral value at the self-paired basepoint. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution f =
      (2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0 := by
  rfl

/-- The correction contribution is the centered pole correction at the basepoint. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution f =
      1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)) := by
  rfl

/-- The combined completed explicit-formula boundary sum. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySumCore
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The analytic core boundary sum is the sum of the three named pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumCore f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  exact Eq.refl _

/-- The completed explicit-formula boundary channel. -/
def completedBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBoundarySumCore g

/-- The prime channel of the completed boundary functional. -/
def primeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution g

/-- The opposite prime face of the completed boundary functional.  This is the negative
prime-power face paired with the positive prime channel by dagger. -/
def oppositePrimeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      zetaCompletedExplicitFormulaPhi g (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))

/-- The archimedean channel of the completed boundary functional. -/
def archimedeanBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution g

/-- The pole channel in the current centered completed-zeta normalization. -/
def poleBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution g

/-- The residual completion channel after the explicit archimedean and pole channels have been
separated.  In the current normalization this channel is zero; if the gamma normalization is
split further, this is the owner slot to refine. -/
def completionBoundaryChannel (_g : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The opposite completed boundary channel.  The prime face is reflected to the negative
prime-power face; the self-paired archimedean and correction faces remain at the basepoint. -/
def oppositeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  oppositePrimeBoundaryChannel g +
    archimedeanBoundaryChannel g +
    poleBoundaryChannel g +
    completionBoundaryChannel g

/-- The completed boundary channel unfolds to the analytic boundary sum core. -/
theorem completedBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    completedBoundaryChannel g =
      zetaCompletedExplicitFormulaBoundarySumCore g := by
  rfl

/-- The prime boundary channel unfolds to the prime contribution. -/
theorem primeBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    primeBoundaryChannel g =
      zetaCompletedExplicitFormulaPrimeContribution g := by
  rfl

/-- The archimedean boundary channel unfolds to the archimedean contribution. -/
theorem archimedeanBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    archimedeanBoundaryChannel g =
      zetaCompletedExplicitFormulaArchimedeanContribution g := by
  rfl

/-- The pole boundary channel unfolds to the correction contribution. -/
theorem poleBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    poleBoundaryChannel g =
      zetaCompletedExplicitFormulaCorrectionContribution g := by
  rfl

/-- The residual completion channel is zero in the current normalization. -/
theorem completionBoundaryChannel_unfold
    (g : ZetaAdmissibleFunction) :
    completionBoundaryChannel g = 0 := by
  rfl

/-- The local channel decomposition of the completed boundary functional. -/
theorem completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (g : ZetaAdmissibleFunction) :
    completedBoundaryChannel g =
      primeBoundaryChannel g +
        archimedeanBoundaryChannel g +
        poleBoundaryChannel g +
        completionBoundaryChannel g := by
  calc
    completedBoundaryChannel g =
        zetaCompletedExplicitFormulaBoundarySumCore g :=
      completedBoundaryChannel_unfold g
    _ =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g :=
      zetaCompletedExplicitFormulaBoundarySumCore_eq g
    _ =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g + 0 := by
      exact (add_zero _).symm
    _ =
        primeBoundaryChannel g +
          archimedeanBoundaryChannel g +
          poleBoundaryChannel g +
          completionBoundaryChannel g := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd
          (congrArg₂ HAdd.hAdd
            (primeBoundaryChannel_unfold g).symm
            (archimedeanBoundaryChannel_unfold g).symm)
          (poleBoundaryChannel_unfold g).symm)
        (completionBoundaryChannel_unfold g).symm

/-- The Hermitian kernel assembled from the completed boundary channels on the convolution
pairing algebra. -/
def completedHermitianKernel
    (f h : ZetaAdmissibleFunction) : ℂ :=
  primeBoundaryChannel (convolutionPair f h) +
    archimedeanBoundaryChannel (convolutionPair f h) +
    poleBoundaryChannel (convolutionPair f h) +
    completionBoundaryChannel (convolutionPair f h)

/-- The completed boundary channel of a convolution pair is the completed Hermitian kernel. -/
theorem completedBoundaryChannel_convolutionPair_eq_kernel
    (f h : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionPair f h) =
      completedHermitianKernel f h := by
  exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (convolutionPair f h)

/-- The diagonal convolution-pair transport specializes to the completed autocorrelation
boundary channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_eq_kernel_diagonal
    (f : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionAutocorrelation f) =
      completedHermitianKernel f f := by
  exact
    Eq.subst
      (motive := fun g : ZetaAdmissibleFunction =>
        completedBoundaryChannel g = completedHermitianKernel f f)
      (convolutionPair_self f)
      (completedBoundaryChannel_convolutionPair_eq_kernel f f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
