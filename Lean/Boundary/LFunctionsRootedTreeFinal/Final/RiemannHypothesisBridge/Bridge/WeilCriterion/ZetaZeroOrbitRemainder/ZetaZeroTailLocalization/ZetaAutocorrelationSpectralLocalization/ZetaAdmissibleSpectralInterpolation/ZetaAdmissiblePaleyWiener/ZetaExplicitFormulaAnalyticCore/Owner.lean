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

/-- One completed prime-power spectral-sample coordinate in the contour-side presentation. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
    -((ZetaPrimePowerIndex.weight ι : ℂ) *
      (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) +
        star (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι))))

/-- The paired seed-transform prime-power coordinate obtained by unfolding the
autocorrelation spectral sample. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
    -((ZetaPrimePowerIndex.weight ι : ℂ) *
      ((zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
          star
            (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ)))) +
        star
          (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
            star
              (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))))))

/-- The oriented seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.weight ι : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
      star
        (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))))

/-- The opposite oriented seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.weight ι : ℂ) *
    (zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ)) *
      star (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)))

/-- The symmetrized seed-transform cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
    star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)

/-- Rectangular finite-window sum of the oriented autocorrelation cross coordinates. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.box N,
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f

/-- Rectangular finite-window sum of the opposite oriented autocorrelation cross coordinates. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossBoxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.box N,
    zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f

/-- The real part of one rectangular oriented-cross prime-power window. -/
noncomputable def zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)

/-- The paired spectral sample is the negative symmetrized cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f =
      -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f := by
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ := zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))
  have hstarW : star W = W := by
    unfold W
    exact Complex.conj_ofReal (ZetaPrimePowerIndex.weight ι)
  unfold zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
  change -(W * (A * star B + star (A * star B))) = -(W * (A * star B) + star (W * (A * star B)))
  have hstar :
      star (W * (A * star B)) = W * star (A * star B) := by
    calc
      star (W * (A * star B)) = star (A * star B) * star W := by
        exact star_mul W (A * star B)
      _ = star (A * star B) * W := by
        exact congrArg (fun z : ℂ => star (A * star B) * z) hstarW
      _ = W * star (A * star B) := by
        exact mul_comm (star (A * star B)) W
  exact congrArg Neg.neg
    (calc
      W * (A * star B + star (A * star B)) =
          W * (A * star B) + W * star (A * star B) := by
        exact mul_add W (A * star B) (star (A * star B))
      _ = W * (A * star B) + star (W * (A * star B)) := by
        exact congrArg (fun z : ℂ => W * (A * star B) + z) hstar.symm)

/-- Conjugating an oriented cross coordinate gives the opposite oriented face. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f := by
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ := zetaCompletedExplicitFormulaPhi f (-(ZetaPrimePowerIndex.center ι : ℂ))
  have hstarW : star W = W := by
    unfold W
    exact Complex.conj_ofReal (ZetaPrimePowerIndex.weight ι)
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
  change star (W * (A * star B)) = W * (B * star A)
  calc
    star (W * (A * star B)) = star (A * star B) * star W := by
      exact star_mul W (A * star B)
    _ = star (A * star B) * W := by
      exact congrArg (fun z : ℂ => star (A * star B) * z) hstarW
    _ = (star (star B) * star A) * W := by
      exact congrArg (fun z : ℂ => z * W) (star_mul A (star B))
    _ = (B * star A) * W := by
      exact congrArg (fun z : ℂ => (z * star A) * W) (star_star B)
    _ = W * (B * star A) := by
      exact mul_comm (B * star A) W

/-- Autocorrelation prime-power spectral coordinates unfold to paired seed-transform
coordinates. -/
theorem zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate
  unfold zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate
  exact congrArg
    (fun z : ℂ =>
      -((ZetaPrimePowerIndex.weight ι : ℂ) * (z + star z)))
    (zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
      f (ZetaPrimePowerIndex.center ι))

/-- The completed prime-power spectral-sample presentation indexed by genuine prime-power
coordinates.  This is the Laplace/contour-side presentation and is deliberately not the owner
real prime distribution: the final explicit-formula prime channel samples the completed
time/log-side boundary value. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι f

/-- Seed-pair real-axis spectral majorant assembled from the two one-sided
prime-power-center spectral majorants. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant_of_oneSided
    (f : ZetaAdmissibleFunction)
    (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hCpos : 0 ≤ Cpos) (hCneg : 0 ≤ Cneg)
    (hpos :
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ ≤
          Cpos * ZetaPrimePowerIndex.polynomialHeightDecay kpos ι)
    (hneg :
      ∀ ι : ZetaPrimePowerIndex,
        ‖star
          (zetaCompletedExplicitFormulaPhi f
            (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
          Cneg * ZetaPrimePowerIndex.polynomialHeightDecay kneg ι) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  refine ⟨Cpos * Cneg, kpos, ?_, ?_⟩
  · exact mul_nonneg hCpos hCneg
  · intro ι
    let A : ℝ :=
      ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖
    let B : ℝ :=
      ‖star
        (zetaCompletedExplicitFormulaPhi f
          (-(ZetaPrimePowerIndex.center ι : ℂ)))‖
    let Dpos : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kpos ι
    let Dneg : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay kneg ι
    have hA_nonneg : 0 ≤ A := norm_nonneg _
    have hB_nonneg : 0 ≤ B := norm_nonneg _
    have hDpos_nonneg : 0 ≤ Dpos :=
      ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kpos ι
    have hDneg_le_one : Dneg ≤ 1 :=
      ZetaPrimePowerIndex.polynomialHeightDecay_le_one kneg ι
    have hpos_ι : A ≤ Cpos * Dpos := hpos ι
    have hneg_ι : B ≤ Cneg * Dneg := hneg ι
    have hCposDpos_nonneg : 0 ≤ Cpos * Dpos :=
      mul_nonneg hCpos hDpos_nonneg
    have hmul_bounds : A * B ≤ (Cpos * Dpos) * (Cneg * Dneg) :=
      mul_le_mul hpos_ι hneg_ι hB_nonneg hCposDpos_nonneg
    have hDneg_nonneg : 0 ≤ Dneg :=
      ZetaPrimePowerIndex.polynomialHeightDecay_nonnegative kneg ι
    have hCnegDneg_le_Cneg : Cneg * Dneg ≤ Cneg * 1 :=
      mul_le_mul_of_nonneg_left hDneg_le_one hCneg
    have hright_shrink :
        (Cpos * Dpos) * (Cneg * Dneg) ≤ (Cpos * Dpos) * (Cneg * 1) :=
      mul_le_mul_of_nonneg_left hCnegDneg_le_Cneg hCposDpos_nonneg
    have halgebra :
        (Cpos * Dpos) * (Cneg * 1) = (Cpos * Cneg) * Dpos := by
      calc
        (Cpos * Dpos) * (Cneg * 1) = (Cpos * Dpos) * Cneg := by
          exact congrArg (fun x : ℝ => (Cpos * Dpos) * x) (mul_one Cneg)
        _ = Cneg * (Cpos * Dpos) := by
          exact mul_comm (Cpos * Dpos) Cneg
        _ = (Cneg * Cpos) * Dpos := by
          exact mul_assoc Cneg Cpos Dpos
        _ = (Cpos * Cneg) * Dpos := by
          exact congrArg (fun x : ℝ => x * Dpos) (mul_comm Cneg Cpos)
    exact hmul_bounds.trans (hright_shrink.trans (le_of_eq halgebra))

/-- Two-sided real-axis rapid decay of the completed spectral transform at prime-power
centers.

This is the Paley-Wiener rapid-decay input on the unbounded real axis: both the
positive centers and their reflected negative centers admit a common polynomial-height
majorant. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_twoSided_realAxisRapidDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        (∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) ∧
        (∀ ι : ZetaPrimePowerIndex,
          ‖star
            (zetaCompletedExplicitFormulaPhi f
              (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) := by
  sorry

/-- Positive real-axis one-sided spectral majorant at prime-power centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_positive_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f
              (ZetaPrimePowerIndex.center ι)‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_twoSided_realAxisRapidDecay f with
  | ⟨C, k, hC, hpositive, _hnegative⟩ =>
      exact ⟨C, k, hC, hpositive⟩

/-- Reflected negative real-axis one-sided spectral majorant at prime-power
centers. -/
theorem zetaCompletedExplicitFormulaPhi_primePower_negative_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖star
            (zetaCompletedExplicitFormulaPhi f
              (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_twoSided_realAxisRapidDecay f with
  | ⟨C, k, hC, _hpositive, hnegative⟩ =>
      exact ⟨C, k, hC, hnegative⟩

/-- Real-axis prime-power spectral seed-pair summability majorant.

This is the real-axis estimate for the spectral/Laplace prime sample.  It is
not a consequence of the vertical-strip Paley-Wiener theorem, which controls decay in
`z.im` on bounded real strips rather than polynomial decay of `Φ_f(log p^n)` on the
unbounded positive real axis. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 ≤ C ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
            C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  match zetaCompletedExplicitFormulaPhi_primePower_positive_realAxisSpectralMajorant f with
  | ⟨Cpos, kpos, hCpos, hpos⟩ =>
      match zetaCompletedExplicitFormulaPhi_primePower_negative_realAxisSpectralMajorant f with
      | ⟨Cneg, kneg, hCneg, hneg⟩ =>
          exact
            zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant_of_oneSided
              f Cpos Cneg kpos kneg hCpos hCneg hpos hneg

/-- Real-axis spectral seed-pair majorant at prime-power centers, in the real norm shape
needed by the paired seed estimate. -/
theorem zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant'
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
            ‖star
              (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, _hC, hbound⟩ :=
    zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
      f
  exact ⟨C, k, hbound⟩

/-- Prime-power weights are absorbed into the seed-pair rapid-decay polynomial height. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_from_seedPairDecay
    (f : ZetaAdmissibleFunction)
    (hseed :
      ∃ C : ℝ, ∃ k : ℕ,
        0 ≤ C ∧
          ∀ ι : ZetaPrimePowerIndex,
            ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
                ‖star
                  (zetaCompletedExplicitFormulaPhi f
                    (-(ZetaPrimePowerIndex.center ι : ℂ)))‖ ≤
              C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖ *
            (‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖) ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, hC_nonneg, hseed_bound⟩ := hseed
  obtain ⟨A, l, hA_nonneg, _hkl, hweight_bound⟩ :=
    ZetaPrimePowerIndex.weight_norm_mul_polynomialHeightDecay_le_shift k
  refine ⟨C * A, l, ?_⟩
  intro ι
  let W : ℝ := ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖
  let P : ℝ :=
    ‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
      ‖star
        (zetaCompletedExplicitFormulaPhi f
          (-(ZetaPrimePowerIndex.center ι : ℂ)))‖
  let Dk : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay k ι
  let Dl : ℝ := ZetaPrimePowerIndex.polynomialHeightDecay l ι
  have hW_nonneg : 0 ≤ W := norm_nonneg _
  have hseed_ι : P ≤ C * Dk := hseed_bound ι
  have hmul_seed : W * P ≤ W * (C * Dk) :=
    mul_le_mul_of_nonneg_left hseed_ι hW_nonneg
  have hcomm : W * (C * Dk) = C * (W * Dk) := by
    calc
      W * (C * Dk) = (W * C) * Dk := by
        exact (mul_assoc W C Dk).symm
      _ = (C * W) * Dk := by
        exact congrArg (fun x : ℝ => x * Dk) (mul_comm W C)
      _ = C * (W * Dk) := by
        exact mul_assoc C W Dk
  have hweight_ι : W * Dk ≤ A * Dl := hweight_bound ι
  have hscaled : C * (W * Dk) ≤ C * (A * Dl) :=
    mul_le_mul_of_nonneg_left hweight_ι hC_nonneg
  have htarget : C * (A * Dl) = C * A * Dl := by
    exact (mul_assoc C A Dl).symm
  exact hmul_seed.trans
    ((le_of_eq hcomm).trans
      (hscaled.trans (le_of_eq htarget)))

/-- Real-norm Paley-Wiener majorant for the weighted seed-pair prime-power coordinate. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ)‖ *
            (‖zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)‖ *
              ‖star
                (zetaCompletedExplicitFormulaPhi f
                  (-(ZetaPrimePowerIndex.center ι : ℂ)))‖) ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_from_seedPairDecay
      f
      (zetaCompletedExplicitFormulaPhi_primePowerSeedPair_realNorm_realAxisSpectralMajorant
        f)

/-- Paley-Wiener prime-power seed-pair estimate for the weighted oriented cross coordinate. -/
theorem zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_norm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖(ZetaPrimePowerIndex.weight ι : ℂ) *
          (zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι) *
            star
              (zetaCompletedExplicitFormulaPhi f
                (-(ZetaPrimePowerIndex.center ι : ℂ))))‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  obtain ⟨C, k, hmajorant⟩ :=
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_realNorm_le_polynomialHeightDecay
      f
  refine ⟨C, k, ?_⟩
  intro ι
  let W : ℂ := (ZetaPrimePowerIndex.weight ι : ℂ)
  let A : ℂ := zetaCompletedExplicitFormulaPhi f (ZetaPrimePowerIndex.center ι)
  let B : ℂ :=
    star
      (zetaCompletedExplicitFormulaPhi f
        (-(ZetaPrimePowerIndex.center ι : ℂ)))
  have hnorm :
      ‖W * (A * B)‖ = ‖W‖ * (‖A‖ * ‖B‖) := by
    calc
      ‖W * (A * B)‖ = ‖W‖ * ‖A * B‖ := by
        exact norm_mul W (A * B)
      _ = ‖W‖ * (‖A‖ * ‖B‖) := by
        exact congrArg (fun x : ℝ => ‖W‖ * x) (norm_mul A B)
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
    hnorm.symm
    (hmajorant ι)

/-- The oriented autocorrelation cross coordinate has a polynomial-height majorant. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_norm_le_polynomialHeightDecay
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      ∀ ι : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    zetaCompletedExplicitFormulaPhi_weightedPrimePowerSeedPair_norm_le_polynomialHeightDecay
      f

/-- The oriented autocorrelation cross coordinate family is summable over raw prime-power
indices. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) := by
  obtain ⟨C, k, hbound⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_norm_le_polynomialHeightDecay
      f
  have hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι) :=
    ZetaPrimePowerIndex.summable_const_mul_polynomialHeightDecay C k
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        C * ZetaPrimePowerIndex.polynomialHeightDecay k ι)
      hmajorant
      hbound

/-- The opposite oriented autocorrelation cross coordinate family is summable over raw
prime-power indices. -/
theorem zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
  have horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    horiented.star
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) =
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
    funext ι
    exact
      (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        ι f).symm
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ => Summable u)
    hpoint.symm
    hstar

/-- A complex number equal to the negative of its conjugate has zero real part. -/
theorem complex_re_eq_zero_of_star_eq_neg
    (z : ℂ) (hz : star z = -z) :
    Complex.re z = 0 := by
  have hcongr :
      Complex.re (star z) = Complex.re (-z) :=
    congrArg Complex.re hz
  have hstar : Complex.re (star z) = Complex.re z := by
    exact Eq.trans
      (congrArg Complex.re (Complex.star_def z))
      (Complex.conj_re z)
  have hneg : Complex.re (-z) = -Complex.re z :=
    Complex.neg_re z
  have hz_neg : Complex.re z = -Complex.re z :=
    hstar.symm.trans (hcongr.trans hneg)
  have hadd : Complex.re z + Complex.re z = 0 :=
    eq_neg_iff_add_eq_zero.mp hz_neg
  have hmul : (2 : ℝ) * Complex.re z = 0 :=
    (two_mul (Complex.re z)).symm.trans hadd
  exact (mul_eq_zero.mp hmul).resolve_left two_ne_zero

/-- A complex number with zero real part is the negative of its conjugate. -/
theorem complex_star_eq_neg_of_re_eq_zero
    (z : ℂ) (hz : Complex.re z = 0) :
    star z = -z := by
  apply Complex.ext
  · calc
      Complex.re (star z) = Complex.re z := by
        exact Eq.trans
          (congrArg Complex.re (Complex.star_def z))
          (Complex.conj_re z)
      _ = 0 := hz
      _ = -0 := by
        exact (neg_zero : -(0 : ℝ) = 0).symm
      _ = -Complex.re z := by
        exact congrArg Neg.neg hz.symm
      _ = Complex.re (-z) := by
        exact (Complex.neg_re z).symm
  · calc
      Complex.im (star z) = -Complex.im z := by
        exact Eq.trans
          (congrArg Complex.im (Complex.star_def z))
          (Complex.conj_im z)
      _ = Complex.im (-z) := by
        exact (Complex.neg_im z).symm

/-- A complex number plus its conjugate is twice its real part. -/
theorem complex_add_star_eq_two_re
    (z : ℂ) :
    z + star z = ((2 : ℝ) * Complex.re z : ℂ) := by
  apply Complex.ext
  · calc
      Complex.re (z + star z) = Complex.re z + Complex.re (star z) := by
        exact Complex.add_re z (star z)
      _ = Complex.re z + Complex.re z := by
        exact congrArg (fun x : ℝ => Complex.re z + x)
          (Eq.trans
            (congrArg Complex.re (Complex.star_def z))
            (Complex.conj_re z))
      _ = (2 : ℝ) * Complex.re z := by
        exact (two_mul (Complex.re z)).symm
      _ = Complex.re (((2 : ℝ) * Complex.re z : ℝ) : ℂ) := by
        exact (Complex.ofReal_re ((2 : ℝ) * Complex.re z)).symm
  · calc
      Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
        exact Complex.add_im z (star z)
      _ = Complex.im z + -Complex.im z := by
        exact congrArg (fun x : ℝ => Complex.im z + x)
          (Eq.trans
            (congrArg Complex.im (Complex.star_def z))
            (Complex.conj_im z))
      _ = 0 := by
        exact add_neg_cancel (Complex.im z)
      _ = Complex.im (((2 : ℝ) * Complex.re z : ℝ) : ℂ) := by
        exact (Complex.ofReal_im ((2 : ℝ) * Complex.re z)).symm

/-- The finite two-face cross sum is the real shadow of the oriented face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) =
      ∑ ι in ZetaPrimePowerIndex.box N,
        ((2 : ℝ) *
          Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
  exact Finset.sum_congr
    rfl
    (fun ι _ =>
      (congrArg
        (fun z : ℂ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f + z)
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
          ι f).symm).trans
        (complex_add_star_eq_two_re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)))

/-- Source contour-tomography estimate for the rectangular real-shadow windows.

This is the direct completed vertical-face cancellation statement: the finite
rectangular real shadows tend to zero in the completed boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) := by
  sorry

/-- Upstream contour-tomography cancellation for the completed oriented
prime-power cross total.

This is the analytic input owned by the completed vertical-face residue ledger:
the two oriented faces pair with opposite orientation, so the completed oriented
cross total is anti-self-conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex, u ι
  have hsummable : Summable u := by
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
        f
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N, u ι)
        Filter.atTop
        (𝓝 z) := by
    unfold z
    exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hboxRe :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (∑ ι in ZetaPrimePowerIndex.box N, u ι))
        Filter.atTop
        (𝓝 (Complex.re z)) :=
    (Complex.continuous_re.tendsto z).comp hbox
  have htwoRe :
      Filter.Tendsto
        (fun N : ℕ =>
          ((2 : ℝ) *
            Complex.re (∑ ι in ZetaPrimePowerIndex.box N, u ι) : ℂ))
        Filter.atTop
        (𝓝 ((2 : ℝ) * Complex.re z : ℂ)) := by
    have hmul :
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re (∑ ι in ZetaPrimePowerIndex.box N, u ι))
          Filter.atTop
          (𝓝 ((2 : ℝ) * Complex.re z)) :=
      Filter.Tendsto.const_mul (2 : ℝ) hboxRe
    exact (Complex.continuous_ofReal.tendsto
      ((2 : ℝ) * Complex.re z)).comp hmul
  have hrealShadow_fun :
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
      (fun N : ℕ =>
        ((2 : ℝ) *
          Complex.re (∑ ι in ZetaPrimePowerIndex.box N, u ι) : ℂ)) := by
    funext N
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum
        N f
  have hsource :
      Filter.Tendsto
        (fun N : ℕ =>
          ((2 : ℝ) *
            Complex.re (∑ ι in ZetaPrimePowerIndex.box N, u ι) : ℂ))
        Filter.atTop
        (𝓝 0) := by
    exact Eq.subst
      (motive := fun v : ℕ → ℂ =>
        Filter.Tendsto v Filter.atTop (𝓝 0))
      hrealShadow_fun
      (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
        f)
  have hlim_eq :
      ((2 : ℝ) * Complex.re z : ℂ) = 0 :=
    tendsto_nhds_unique htwoRe hsource
  have hreal_two_zero :
      (2 : ℝ) * Complex.re z = 0 := by
    calc
      (2 : ℝ) * Complex.re z =
          Complex.re (((2 : ℝ) * Complex.re z : ℝ) : ℂ) := by
            exact (Complex.ofReal_re ((2 : ℝ) * Complex.re z)).symm
      _ = Complex.re (0 : ℂ) := by
            exact congrArg Complex.re hlim_eq
      _ = 0 := by
            exact Complex.zero_re
  have hre : Complex.re z = 0 :=
    (mul_eq_zero.mp hreal_two_zero).resolve_left two_ne_zero
  have hanti : star z = -z :=
    complex_star_eq_neg_of_re_eq_zero z hre
  unfold z at hanti
  unfold u at hanti
  exact hanti

/-- The paired autocorrelation spectral-sample total is the negative of the
oriented cross total plus its conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_neg_oriented_add_star
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      -((∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) +
        star
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f
  let symm : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex => u ι + star (u ι)
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar :
      (∑' ι : ZetaPrimePowerIndex, star (u ι)) =
        star (∑' ι : ZetaPrimePowerIndex, u ι) :=
    hu.tsum_star.symm
  have hsymm_tsum :
      (∑' ι : ZetaPrimePowerIndex, symm ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) +
          star (∑' ι : ZetaPrimePowerIndex, u ι) := by
    have hsum_add :
        (∑' ι : ZetaPrimePowerIndex, symm ι) =
          (∑' ι : ZetaPrimePowerIndex, u ι) +
            (∑' ι : ZetaPrimePowerIndex, star (u ι)) := by
      unfold symm
      exact (hu.tsum_add hu.star).symm
    exact hsum_add.trans
      (congrArg
        (fun z : ℂ => (∑' ι : ZetaPrimePowerIndex, u ι) + z)
        hstar)
  have hpaired_eq_neg_symm :
      paired = fun ι : ZetaPrimePowerIndex => -symm ι := by
    funext ι
    unfold paired
    unfold symm
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hpaired_tsum :
      (∑' ι : ZetaPrimePowerIndex, paired ι) =
        ∑' ι : ZetaPrimePowerIndex, -symm ι := by
    exact congrArg
      (fun v : ZetaPrimePowerIndex → ℂ =>
        ∑' ι : ZetaPrimePowerIndex, v ι)
      hpaired_eq_neg_symm
  have hsymm_summable : Summable symm :=
    hu.add hu.star
  have hneg_tsum :
      (∑' ι : ZetaPrimePowerIndex, -symm ι) =
        -(∑' ι : ZetaPrimePowerIndex, symm ι) :=
    hsymm_summable.tsum_neg
  calc
    (∑' ι : ZetaPrimePowerIndex, paired ι)
        = ∑' ι : ZetaPrimePowerIndex, -symm ι := hpaired_tsum
    _ = -(∑' ι : ZetaPrimePowerIndex, symm ι) := hneg_tsum
    _ =
        -((∑' ι : ZetaPrimePowerIndex, u ι) +
          star (∑' ι : ZetaPrimePowerIndex, u ι)) := by
          exact congrArg Neg.neg hsymm_tsum

/-- The paired autocorrelation spectral-sample total vanishes from the
anti-self-conjugacy of the oriented cross total. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_zero_of_oriented_tsum_star_eq_neg
    (f : ZetaAdmissibleFunction)
    (horiented :
      star
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
        -∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      0 := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hpaired :
      (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
        -(z + star z) := by
    unfold z
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_neg_oriented_add_star
        f
  have hsum_zero : z + star z = 0 := by
    calc
      z + star z = z + -z := by
        exact congrArg (fun w : ℂ => z + w) horiented
      _ = 0 := by
        exact add_neg_cancel z
  calc
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
        = -(z + star z) := hpaired
    _ = -0 := by
        exact congrArg Neg.neg hsum_zero
    _ = 0 := by
        exact neg_zero

/-- The autocorrelation spectral-sample total is the paired seed-transform
total. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_tsum_convolutionAutocorrelation_eq_paired_tsum
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      ∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  exact congrArg
    (fun v : ZetaPrimePowerIndex → ℂ =>
      ∑' ι : ZetaPrimePowerIndex, v ι)
    hpoint

/-- Completed autocorrelation prime-power symmetrized cross-coordinate cancellation.

This is the owner contour-tomography form of the vertical-face pairing: the
symmetrized oriented cross series has zero completed sum. -/
theorem zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_eq_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f) = 0 := by
  calc
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
          exact rfl
    _ =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
          exact
            zetaCompletedPrimePowerSpectralSampleCoordinate_tsum_convolutionAutocorrelation_eq_paired_tsum
              f
    _ = 0 := by
          exact
            zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_zero_of_oriented_tsum_star_eq_neg
              f
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
                f)

/-- Summability of the autocorrelation prime-power spectral sample follows from
the oriented cross-coordinate majorant and the paired-coordinate normal form. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_summable_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let symm : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f
  let spectral : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar : Summable (fun ι : ZetaPrimePowerIndex => star (u ι)) :=
    hu.star
  have hsymm_raw :
      Summable (fun ι : ZetaPrimePowerIndex => u ι + star (u ι)) :=
    hu.add hstar
  have hsymm_point :
      (fun ι : ZetaPrimePowerIndex => u ι + star (u ι)) = symm := by
    funext ι
    unfold u
    unfold symm
    rfl
  have hsymm : Summable symm :=
    Eq.subst
      (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
      hsymm_point
      hsymm_raw
  have hpaired_neg : Summable (fun ι : ZetaPrimePowerIndex => -symm ι) :=
    hsymm.neg
  have hpaired_point :
      paired = (fun ι : ZetaPrimePowerIndex => -symm ι) := by
    funext ι
    unfold paired
    unfold symm
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hpaired : Summable paired :=
    Eq.subst
      (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
      hpaired_point.symm
      hpaired_neg
  have hspectral_point : spectral = paired := by
    funext ι
    unfold spectral
    unfold paired
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  unfold spectral at hspectral_point
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
    hspectral_point.symm
    hpaired

/-- Completed autocorrelation prime-power spectral-sample cancellation as a
`HasSum` statement. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      0 := by
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_summable_convolutionAutocorrelation
      f
  have hzero :
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_eq_zero_contourTomography
        f
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        z)
    hzero
    hsummable.hasSum

/-- Completed autocorrelation prime-power paired spectral-sample cancellation.

This transports the contour-tomography spectral-sample cancellation through the
autocorrelation paired-coordinate normal form. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
      0 := by
  have hspectral :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        0 :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
      f
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ => HasSum u 0)
    hpoint
    hspectral

/-- Completed autocorrelation prime-power symmetrized cross-coordinate cancellation.

This is the algebraic sign transport from the paired spectral-sample coordinate
to the symmetrized oriented cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
      0 := by
  have hpaired :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
        0 :=
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
      f
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      (fun ι : ZetaPrimePowerIndex =>
        -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hneg :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        0 :=
    Eq.subst
      (motive := fun u : ZetaPrimePowerIndex → ℂ => HasSum u 0)
      hpoint
      hpaired
  have hsymNeg :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        (-0) :=
    hneg.neg
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        z)
    neg_zero
    hsymNeg

/-- The completed oriented cross-coordinate total is anti-self-conjugate.

This is the upstream contour-tomography cancellation: after the completed
residue ledger pairs the two oriented vertical faces, the oriented prime-power
cross total equals the negative of its conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
      f

/-- Rectangular real-shadow windows are twice the real part of the rectangular
oriented-cross window. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f) : ℂ) := by
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
  calc
    (∑ ι in ZetaPrimePowerIndex.box N,
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
        ((∑ ι in ZetaPrimePowerIndex.box N,
          (2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℝ) : ℂ) := by
      exact Finset.sum_ofReal
        (ZetaPrimePowerIndex.box N)
        (fun ι : ZetaPrimePowerIndex =>
          (2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
    _ =
        ((2 : ℝ) *
          (∑ ι in ZetaPrimePowerIndex.box N,
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) : ℝ) := by
      exact congrArg
        (fun r : ℝ => (r : ℂ))
        (Finset.mul_sum
          (ZetaPrimePowerIndex.box N)
          (fun ι : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
          (2 : ℝ)).symm
    _ =
        ((2 : ℝ) *
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
      exact congrArg
        (fun r : ℝ => ((2 : ℝ) * r : ℝ) : ℂ)
        (Complex.sum_re
          (ZetaPrimePowerIndex.box N)
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)).symm

/-- The completed contour-tail real shadow of the oriented prime-power face vanishes.

This is the contour-tomography estimate: the analytic core owns the finite oriented
cross-coordinate algebra, while the vanishing limit must be supplied by the downstream
contour/residue ledger normalization. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
      f

/-- Public analytic-core wrapper for the contour-tomography real-shadow cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) :=
  zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
    f

/-- Rectangular windows of the two opposite oriented faces cancel in the completed boundary
limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      Filter.atTop
      (𝓝 0) := by
  have hshadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (𝓝 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_boundaryCancellation
      f
  have hfun :
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) =
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (𝓝 0))
    hfun.symm
    hshadow

/-- The sum of the two oriented-face series is zero in the completed boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      0 := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hv : Summable v := by
    unfold v
    exact zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable f
  have huv : Summable (fun ι : ZetaPrimePowerIndex => u ι + v ι) :=
    hu.add hv
  have hbox_tsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N, u ι + v ι)
        Filter.atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι + v ι)) :=
    huv.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hbox_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N, u ι + v ι)
        Filter.atTop
        (𝓝 0) := by
    have hcancel :=
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_boundaryCancellation
        f
    unfold u
    unfold v
    exact hcancel
  have htsum_zero :
      (∑' ι : ZetaPrimePowerIndex, u ι + v ι) = 0 :=
    tendsto_nhds_unique hbox_tsum hbox_zero
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) z)
    htsum_zero
    huv.hasSum

/-- The opposite oriented prime-power boundary face cancels the positive oriented face in the
completed boundary pairing. -/
theorem zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_hasSum_neg_tsum_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      (-(∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f
  have hsum :
      HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) 0 := by
    unfold u
    unfold v
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_boundaryCancellation
        f
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hv : Summable v := by
    unfold v
    exact zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_summable f
  have htarget :
      (0 : ℂ) = (∑' ι : ZetaPrimePowerIndex, u ι) +
          (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
    exact (add_neg_cancel (∑' ι : ZetaPrimePowerIndex, u ι)).symm
  have hv_sum :
      HasSum v (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
    have hadd :
        HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι)
          ((∑' ι : ZetaPrimePowerIndex, u ι) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))) := by
      exact Eq.subst
        (motive := fun z : ℂ =>
          HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) z)
        htarget
        hsum
    have hu_sum : HasSum u (∑' ι : ZetaPrimePowerIndex, u ι) :=
      hu.hasSum
    have hneg_u :
        HasSum (fun ι : ZetaPrimePowerIndex => -u ι)
          (-(∑' ι : ZetaPrimePowerIndex, u ι)) :=
      hu_sum.neg
    have hpoint :
        (fun ι : ZetaPrimePowerIndex => u ι + v ι + -u ι) = v := by
      funext ι
      calc
        u ι + v ι + -u ι = v ι + (u ι + -u ι) := by
          exact add_right_comm (u ι) (v ι) (-u ι)
        _ = v ι + 0 := by
          exact congrArg (fun z : ℂ => v ι + z) (add_neg_cancel (u ι))
        _ = v ι := by
          exact add_zero (v ι)
    have hadded :
        HasSum
          (fun ι : ZetaPrimePowerIndex => (u ι + v ι) + -u ι)
          (((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))) :=
      hadd.add hneg_u
    have htarget2 :
        ((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι)) =
          -(∑' ι : ZetaPrimePowerIndex, u ι) := by
      calc
        ((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι)) =
            0 + (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
          exact congrArg
            (fun z : ℂ => z + (-(∑' ι : ZetaPrimePowerIndex, u ι)))
            (add_neg_cancel (∑' ι : ZetaPrimePowerIndex, u ι))
        _ = -(∑' ι : ZetaPrimePowerIndex, u ι) := by
          exact zero_add (-(∑' ι : ZetaPrimePowerIndex, u ι))
    exact Eq.subst
      (motive := fun w : ℂ => HasSum v w)
      htarget2
      (Eq.subst
        (motive := fun w : ZetaPrimePowerIndex → ℂ => HasSum w
          (((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))))
        hpoint
        hadded)
  unfold v at hv_sum
  unfold u at hv_sum
  exact hv_sum

/-- The conjugated oriented-cross coordinate series sums to the negative completed boundary
value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_hasSum_neg_tsum_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      (-(∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  have hopposite :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
        (-(∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_hasSum_neg_tsum_boundaryCancellation
      f
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        ι f
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ =>
      HasSum u
        (-(∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)))
    hpoint.symm
    hopposite

/-- The completed oriented-cross prime-power series is anti-self-conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography
      f

/-- The completed oriented-cross prime-power series has zero real boundary value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) = 0 := by
  exact complex_re_eq_zero_of_star_eq_neg
    (∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
    (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_boundaryCancellation
      f)

/-- The real parts of rectangular oriented-cross windows tend to zero. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart N f)
      Filter.atTop
      (𝓝 0) := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
      f
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (𝓝 z) := by
    unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
    unfold z
    exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hboxRe :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (𝓝 (Complex.re z)) := by
    exact Complex.continuous_re.tendsto z |>.comp hbox
  have hre : Complex.re z = 0 := by
    unfold z
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_re_eq_zero_boundaryCancellation
        f
  change
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
      Filter.atTop
      (𝓝 0)
  exact Eq.subst
    (motive := fun r : ℝ =>
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (𝓝 r))
    hre
    hboxRe

/-- The complex rectangular oriented-cross windows converge to the summable series value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_tsum
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
      Filter.atTop
      (𝓝
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
      f
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
  exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop

/-- The real parts of rectangular oriented-cross windows tend to zero. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_re_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (𝓝 z) ∧
      Complex.re z = 0 := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (𝓝 z) := by
    unfold z
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_tsum f
  have hboxRe :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (𝓝 (Complex.re z)) := by
    exact Complex.continuous_re.tendsto z |>.comp hbox
  have hzero :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (𝓝 0) := by
    change
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart N f)
        Filter.atTop
        (𝓝 0)
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart_tendsto_zero
        f
  have hre : Complex.re z = 0 :=
    tendsto_nhds_unique hboxRe hzero
  exact ⟨z, hbox, hre⟩

/-- Rectangular oriented-cross windows converge to a zero-real completed boundary value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_realPart_zero
    (f : ZetaAdmissibleFunction) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (𝓝 z) ∧
      Complex.re z = 0 := by
  obtain ⟨z, hbox, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_re_tendsto_zero
      f
  refine ⟨z, hbox, hre⟩

/-- Rectangular prime-power oriented cross windows converge to a completed boundary value
with zero real part.

This packages summability with the finite-window boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_boxLimit_realPart_zero
    (f : ZetaAdmissibleFunction) :
    ∃ z : ℂ,
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        Filter.atTop
        (𝓝 z) ∧
      Complex.re z = 0 := by
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable
      f
  obtain ⟨z, hbox, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_realPart_zero
      f
  refine ⟨z, hsummable, ?_, hre⟩
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum at hbox
  exact hbox

/-- The finite-window oriented cross sums determine the completed `HasSum` value with zero
real part. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_of_windowLimit
    (f : ZetaAdmissibleFunction) :
    ∃ z : ℂ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        z ∧
      Complex.re z = 0 := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  obtain ⟨z, hsummable, hbox, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_boxLimit_realPart_zero
      f
  have hbox_tsum :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.box N, u ι)
        Filter.atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) := by
    exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hbox_u :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.box N, u ι)
        Filter.atTop
        (𝓝 z) := by
    unfold u
    exact hbox
  have htsum_eq_z :
      (∑' ι : ZetaPrimePowerIndex, u ι) = z :=
    tendsto_nhds_unique hbox_tsum hbox_u
  refine ⟨z, ?_, hre⟩
  exact Eq.subst
    (motive := fun w : ℂ => HasSum u w)
    htsum_eq_z
    hsummable.hasSum

/-- The oriented autocorrelation cross series has a completed boundary sum with zero real
part. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    ∃ z : ℂ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        z ∧
      Complex.re z = 0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_of_windowLimit
      f

/-- The oriented autocorrelation cross series has purely imaginary completed boundary sum. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_pureImaginary_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    ∃ y : ℝ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        (Complex.I * (y : ℂ)) := by
  obtain ⟨z, hsum, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_boundaryCancellation
      f
  refine ⟨Complex.im z, ?_⟩
  have hz : z = Complex.I * (Complex.im z : ℂ) := by
    apply Complex.ext
    · calc
        Complex.re z = 0 := hre
        _ = Complex.re (Complex.I * (Complex.im z : ℂ)) := by
          exact
            (calc
              Complex.re (Complex.I * (Complex.im z : ℂ)) =
                  -Complex.im (Complex.im z : ℂ) := by
                exact Complex.I_mul_re (Complex.im z : ℂ)
              _ = -0 := by
                exact congrArg Neg.neg (Complex.ofReal_im (Complex.im z))
              _ = 0 := by
                exact neg_zero).symm
    · calc
        Complex.im z = Complex.im z := rfl
        _ = Complex.im (Complex.I * (Complex.im z : ℂ)) := by
          exact
            (calc
              Complex.im (Complex.I * (Complex.im z : ℂ)) =
                  Complex.re (Complex.im z : ℂ) := by
                exact Complex.I_mul_im (Complex.im z : ℂ)
              _ = Complex.im z := by
                exact Complex.ofReal_re (Complex.im z)).symm
  · exact Eq.subst
      (motive := fun w : ℂ =>
        HasSum
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
          w)
      hz
      hsum

/-- Completed autocorrelation prime-power spectral-sample coordinate-sum cancellation.

This is the coordinate-level sink for the completed spectral-sample cancellation on
autocorrelation probes. -/
theorem zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_contourTomography
      f

/-- The paired seed-transform prime-power series cancels once the symmetrized cross series
cancels. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
      f

/-- Completed autocorrelation prime-power spectral-sample coordinate-sum cancellation after
folding the paired seed-transform presentation back to autocorrelation coordinates. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      0 := by
  exact
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
      f

/-- The completed autocorrelation prime-power spectral-sample coordinate sum has zero real
scalar. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinateTsum_convolutionAutocorrelation_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have hsum :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        0 :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
      f
  have htsum :
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 :=
    hsum.tsum_eq
  exact (congrArg Complex.re htsum).trans Complex.zero_re

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
    (f : ZetaAdmissibleFunction) : ℂ :=
  (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
    zetaCompletedExplicitFormulaPhi f 0

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
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f 0 := by
  rfl

/-- The centered correction contribution vanishes on the zero admissible probe. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_zero :
    zetaCompletedExplicitFormulaCorrectionContribution
        (0 : ZetaAdmissibleFunction) = 0 := by
  calc
    zetaCompletedExplicitFormulaCorrectionContribution
        (0 : ZetaAdmissibleFunction) =
        (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
          zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 := by
      exact zetaCompletedExplicitFormulaCorrectionContribution_eq 0
    _ =
        (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * 0 := by
      exact congrArg
        (fun z : ℂ =>
          (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * z)
        (zetaCompletedExplicitFormulaPhi_zero 0)
    _ = 0 := by
      exact mul_zero _

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
