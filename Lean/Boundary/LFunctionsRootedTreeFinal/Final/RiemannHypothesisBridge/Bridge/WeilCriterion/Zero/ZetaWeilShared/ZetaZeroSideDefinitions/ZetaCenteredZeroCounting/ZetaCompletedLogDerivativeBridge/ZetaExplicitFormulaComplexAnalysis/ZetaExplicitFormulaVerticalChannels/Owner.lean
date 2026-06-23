import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.Owner
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary explicit-formula vertical channel owner API

This file owns the vertical realization of the prime, archimedean, and
correction channel packets.  The scheduled contour is the analytic
normalization procedure: it transports a chosen vertical measurement into the
completed boundary-channel object.  The complex-analysis contour assembly file
imports these channel objects and treats the corresponding transport theorems
as owner facts.
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

/-- The prime logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- On the right vertical side of an explicit-formula contour, the prime channel is the
von Mangoldt Dirichlet series. -/
theorem explicitFormulaPrimeLogDerivative_rightPath_eq_vonMangoldt_LSeries
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) =
      L ↗Λ (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = F.c := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t)
      (F.rectangle_c T)
  have hs :
      (1 : ℝ) <
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) < x)
      hre.symm
      F.c_gt_one
  exact
    explicitFormulaPrimeLogDerivative_eq_vonMangoldt_LSeries_of_one_lt_re
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)
      hs

/-- The right vertical prime integrand is the von Mangoldt L-series times the test
transform. -/
theorem zetaCompletedExplicitFormulaPrimeRightIntegrand_eq_vonMangoldt_LSeries
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
    L ↗Λ (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  exact congrArg
    (fun z : ℂ =>
      z *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
    (explicitFormulaPrimeLogDerivative_rightPath_eq_vonMangoldt_LSeries F T t)

/-- The finite-height right prime channel is the von Mangoldt Dirichlet-series integral
on the right side of the contour. -/
theorem zetaCompletedExplicitFormulaPrimeRightIntegral_eq_vonMangoldt_LSeries
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      L ↗Λ (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  exact MeasureTheory.setIntegral_congr_fun
    measurableSet_Icc
    (fun t _ht =>
      zetaCompletedExplicitFormulaPrimeRightIntegrand_eq_vonMangoldt_LSeries
        f F T t)

/-- Finite-height prime-channel normalization after expanding the right logarithmic
derivative as the von Mangoldt Dirichlet series. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_rightVonMangoldtIntegral_sub_left
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaPrimeVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        L ↗Λ (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  let leftIntegral : ℂ :=
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  calc
    zetaCompletedExplicitFormulaPrimeVerticalChannel f F T =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          explicitFormulaPrimeLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
          leftIntegral := by
      rfl
    _ =
        (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          L ↗Λ (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
          leftIntegral := by
      exact congrArg
        (fun z : ℂ => z - leftIntegral)
        (zetaCompletedExplicitFormulaPrimeRightIntegral_eq_vonMangoldt_LSeries
          f F T)

/-- The archimedean logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The pole-correction logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The inverse-Gamma completion logarithmic-derivative vertical channel.

This is the direct owner object for the Gamma/completion transport limit: it is
not decomposed into the archimedean and pole-correction packets until the
finite-height integral identities below are applied. -/
noncomputable def zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- On the right vertical side, the archimedean channel plus the pole-correction
channel is the inverse-Gamma completion logarithmic-derivative integrand. -/
theorem zetaCompletedExplicitFormulaArchimedean_rightIntegrand_add_correction_eq_inverseGammaCompletion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  let s : ℂ := zetaCompletedExplicitFormulaRightPath (F.rectangle T) t
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f (s - 1 / 2)
  let A : ℂ := explicitFormulaArchimedeanLogDerivative s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let G : ℂ := inverseGammaCompletionLogDeriv s
  have hA : A = G - C := by
    exact explicitFormulaArchimedeanLogDerivative_eq_inverseGammaCorrection_sub_poleCorrection s
  have hsum : A + C = G := by
    calc
      A + C = (G - C) + C := by
        exact congrArg (fun z : ℂ => z + C) hA
      _ = G := by
        exact sub_add_cancel G C
  calc
    explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
        A * Φ + C * Φ := by
      exact Eq.refl _
    _ = (A + C) * Φ := by
      exact (add_mul A C Φ).symm
    _ = G * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hsum
    _ =
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
      exact Eq.refl _

/-- On the left vertical side, the archimedean channel plus the pole-correction
channel is the inverse-Gamma completion logarithmic-derivative integrand. -/
theorem zetaCompletedExplicitFormulaArchimedean_leftIntegrand_add_correction_eq_inverseGammaCompletion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  let Φ : ℂ := zetaCompletedExplicitFormulaPhi f (s - 1 / 2)
  let A : ℂ := explicitFormulaArchimedeanLogDerivative s
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let G : ℂ := inverseGammaCompletionLogDeriv s
  have hA : A = G - C := by
    exact explicitFormulaArchimedeanLogDerivative_eq_inverseGammaCorrection_sub_poleCorrection s
  have hsum : A + C = G := by
    calc
      A + C = (G - C) + C := by
        exact congrArg (fun z : ℂ => z + C) hA
      _ = G := by
        exact sub_add_cancel G C
  calc
    explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
        A * Φ + C * Φ := by
      exact Eq.refl _
    _ = (A + C) * Φ := by
      exact (add_mul A C Φ).symm
    _ = G * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hsum
    _ =
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
      exact Eq.refl _

/-- Right vertical integral form of the archimedean-plus-correction
inverse-Gamma completion identity. -/
theorem zetaCompletedExplicitFormulaArchimedean_rightIntegral_add_correction_integrand_eq_inverseGammaCompletion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  exact MeasureTheory.setIntegral_congr_fun
    measurableSet_Icc
    (fun t _ht =>
      zetaCompletedExplicitFormulaArchimedean_rightIntegrand_add_correction_eq_inverseGammaCompletion
        f F T t)

/-- Left vertical integral form of the archimedean-plus-correction
inverse-Gamma completion identity. -/
theorem zetaCompletedExplicitFormulaArchimedean_leftIntegral_add_correction_integrand_eq_inverseGammaCompletion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  exact MeasureTheory.setIntegral_congr_fun
    measurableSet_Icc
    (fun t _ht =>
      zetaCompletedExplicitFormulaArchimedean_leftIntegrand_add_correction_eq_inverseGammaCompletion
        f F T t)

/-- The scheduled inverse-Gamma completion channel is the explicit right-minus-left
vertical integral of the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_scheduled_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
        f F (h.height_schedule.height u) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
  rfl

/-- Early compact-owner nonvanishing of the right vertical path at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero_ownerCompact
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  have hpos : 0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
    exact Eq.symm hre ▸ F.c_pos
  exact fun hzero =>
    have hre_zero :
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    (ne_of_gt hpos) hre_zero

/-- Early compact-owner nonvanishing of the right vertical path at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero_ownerCompact
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  have hgt : 1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
    exact Eq.symm hre ▸ F.c_gt_one
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaRightPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one :
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_gt hgt) hre_one

/-- Early compact-owner nonvanishing of the left vertical path at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero_ownerCompact
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hlt : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 0 := by
    have hraw : 1 - (F.rectangle T).c < 0 :=
      sub_neg.mpr F.c_gt_one
    exact Eq.symm hre ▸ hraw
  exact fun hzero =>
    have hre_zero :
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    (ne_of_lt hlt) hre_zero

/-- Early compact-owner nonvanishing of the left vertical path at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero_ownerCompact
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hlt : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 1 := by
    have hpos : 0 < (F.rectangle T).c :=
      F.c_pos
    exact Eq.symm hre ▸ sub_lt_self (1 : ℝ) hpos
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one :
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_lt hlt) hre_one

/-- Early compact-owner continuity of the shifted completed transform on the right
vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  have hPhiShift :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhiShift.comp hpath

/-- Early compact-owner continuity of the shifted completed transform on the left
vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  have hPhiShift :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhiShift.comp hpath

/-- Early compact-owner right archimedean-channel integrability on a finite height
interval. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaRightPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inl ⟨t, ht, rfl⟩
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous_ownerCompact
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Early compact-owner left archimedean-channel integrability on a finite height
interval. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous_ownerCompact
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Early compact-owner right correction-channel integrability for the original
correction log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.div hpath
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero_ownerCompact F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t =>
          zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero_ownerCompact F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous_ownerCompact f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Early compact-owner left correction-channel integrability for the original
correction log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.div hpath
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero_ownerCompact F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t =>
          zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero_ownerCompact F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous_ownerCompact f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Early fixed-height reconstruction of the inverse-Gamma completion channel from the
archimedean packet and the pole-correction packet. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction_ownerCompact
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T := by
  let S : Set ℝ := Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  let RA : ℂ :=
    ∫ t in S,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RC : ℂ :=
    ∫ t in S,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let LA : ℂ :=
    ∫ t in S,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LC : ℂ :=
    ∫ t in S,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have hRA :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn_ownerCompact
      f hPhi F T havoid
  have hRC :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn_ownerCompact
      f hPhi F T
  have hLA :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn_ownerCompact
      f hPhi F T havoid
  have hLC :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn_ownerCompact
      f hPhi F T
  have hrightAdd :
      (∫ t in S,
        explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        RA + RC := by
    exact integral_add hRA hRC
  have hleftAdd :
      (∫ t in S,
        explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        LA + LC := by
    exact integral_add hLA hLC
  have hrightInv :
      (∫ t in S,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        RA + RC := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaArchimedean_rightIntegral_add_correction_integrand_eq_inverseGammaCompletion
        f F T).symm
      hrightAdd
  have hleftInv :
      (∫ t in S,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        LA + LC := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaArchimedean_leftIntegral_add_correction_integrand_eq_inverseGammaCompletion
        f F T).symm
      hleftAdd
  calc
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T =
        (RA + RC) - (LA + LC) := by
      exact congrArg₂ Sub.sub hrightInv hleftInv
    _ = (RA - LA) + (RC - LC) := by
      exact add_sub_add_comm RA RC LA LC
    _ =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T := by
      rfl

/-- The sum of the three vertical logarithmic-derivative channels. -/
noncomputable def zetaCompletedExplicitFormulaVerticalChannelSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel f F T +
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-! ## Channel transport remainders -/

/-- Prime vertical-channel transport remainder.

The channel-specific convergence theorem is not a consequence of the total residue
identity alone.  The analytic content is the vanishing of this scheduled remainder. -/
noncomputable def zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel f F T -
    zetaCompletedExplicitFormulaPrimeContribution f

/-- The prime vertical channel is its completed contribution plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaPrimeVerticalChannel f F T =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaPrimeVerticalChannel f F T
  let P : ℂ := zetaCompletedExplicitFormulaPrimeContribution f
  change V = P + (V - P)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-P + P) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel P).symm
    _ = (V + -P) + P := by
      exact (add_assoc V (-P) P).symm
    _ = P + (V + -P) := by
      exact add_comm (V + -P) P
    _ = P + (V - P) := by
      exact congrArg (fun x : ℂ => P + x) (sub_eq_add_neg V P).symm

/-- Archimedean vertical-channel transport remainder.

The channel-specific convergence theorem is the vanishing of this scheduled remainder,
after the Gamma/completion channel has been normalized. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T -
    zetaCompletedExplicitFormulaArchimedeanContribution f

/-- The archimedean vertical channel is its completed contribution plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  change V = A + (V - A)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-A + A) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel A).symm
    _ = (V + -A) + A := by
      exact (add_assoc V (-A) A).symm
    _ = A + (V + -A) := by
      exact add_comm (V + -A) A
    _ = A + (V - A) := by
      exact congrArg (fun x : ℂ => A + x) (sub_eq_add_neg V A).symm

/-- The standard-contour correction boundary value obtained from the separated
`s = 0` and `s = 1` pole-face transports.  This is intentionally distinct from
the older centered contribution normalization until the contour-side basepoint
transport theorem identifies them. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionStandardContourContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
    (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)

/-- The standard-contour correction boundary value unfolds to the separated
right-minus-left pole-face residue expression. -/
theorem zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f =
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
  rfl

/-- Pole-correction vertical-channel transport remainder, normalized by the
standard-contour correction boundary value. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T -
    zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

/-- The pole-correction vertical channel is its standard-contour boundary value
plus its transport remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f +
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder f F T := by
  let V : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  change V = C + (V - C)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-C + C) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel C).symm
    _ = (V + -C) + C := by
      exact (add_assoc V (-C) C).symm
    _ = C + (V + -C) := by
      exact add_comm (V + -C) C
    _ = C + (V - C) := by
      exact congrArg (fun x : ℂ => C + x) (sub_eq_add_neg V C).symm

/-! ## Channel realization limit owners -/

/-- The three scheduled vertical channel projections owned by this file. -/
inductive ExplicitFormulaScheduledVerticalChannelProjection where
  | prime
  | archimedean
  | correction

/-- The realized vertical contour integral attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-- The boundary contribution attached to a scheduled channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionContribution
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  match channel with
  | ExplicitFormulaScheduledVerticalChannelProjection.prime =>
      zetaCompletedExplicitFormulaPrimeContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.archimedean =>
      zetaCompletedExplicitFormulaArchimedeanContribution f
  | ExplicitFormulaScheduledVerticalChannelProjection.correction =>
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f

/-- The transport remainder attached to a scheduled vertical channel projection. -/
noncomputable def explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionIntegral f F T channel -
    explicitFormulaScheduledVerticalChannelProjectionContribution f channel

/-- The scheduled projected vertical-decomposition error is exactly the selected channel
transport remainder already defined from the concrete vertical channel integrals. -/
noncomputable def explicitFormulaScheduledProjectedVerticalDecompositionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
    f F (h.height_schedule.height u) channel

/-- The selected-channel projected vertical decomposition is definitionally the scheduled
transport remainder at the chosen height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u) channel := by
  rfl

/-- The prime scheduled projection transport remainder is the concrete prime
vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder f F T := by
  rfl

/-- The archimedean scheduled projection transport remainder is the concrete
archimedean vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder f F T := by
  rfl

/-- The correction scheduled projection transport remainder is the concrete
correction vertical-channel transport remainder. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F T ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder f F T := by
  rfl

/-- The projected prime vertical-decomposition error is the scheduled concrete prime
transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.prime := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime
    _ = zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_prime_eq
            f F (h.height_schedule.height u)

/-- The projected archimedean vertical-decomposition error is the scheduled concrete
archimedean transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.archimedean := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean
    _ = zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
            f F (h.height_schedule.height u)

/-- The projected correction vertical-decomposition error is the scheduled concrete
correction transport remainder at the analytic-package height. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
  calc
    explicitFormulaScheduledProjectedVerticalDecompositionError
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
        f F (h.height_schedule.height u)
          ExplicitFormulaScheduledVerticalChannelProjection.correction := by
        exact
          explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction
    _ = zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
        f F (h.height_schedule.height u) := by
        exact
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
            f F (h.height_schedule.height u)

/-- Prime projected vertical-decomposition convergence follows from the exact concrete
prime transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_prime_tendsto_zero_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_prime_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-- Archimedean projected vertical-decomposition convergence follows from the exact
concrete archimedean transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_tendsto_zero_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_archimedean_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-- Correction projected vertical-decomposition convergence follows from the exact
concrete correction transport-remainder convergence, by pointwise projection only. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_correction_tendsto_zero_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
            f F (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaScheduledProjectedVerticalDecompositionError_correction_eq f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    htransport

/-! ## Component contour-estimate analytic inputs -/

/-- The scheduled rectangle boundary integral at the package height. -/
noncomputable def explicitFormulaScheduledRectangleContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f
    (F.rectangle (h.height_schedule.height u))

/-- The scheduled finite completed-zero residue sum at the package height. -/
noncomputable def explicitFormulaScheduledRectangleResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  explicitFormulaCompletedZeroHeightWindowResidueSum f
    (h.height_schedule.height u)

/-- The finite rectangle residue equality along the selected schedule. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_residueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.toContourFamily.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleContourIntegral f F.toContourFamily h u =
      explicitFormulaScheduledRectangleResidueSum f F.toContourFamily h u := by
  calc
    explicitFormulaScheduledRectangleContourIntegral f F.toContourFamily h u =
      zetaCompletedExplicitFormulaContourIntegral f
        (F.toContourFamily.rectangle (h.height_schedule.height u)) := by
        rfl
    _ = explicitFormulaCompletedZeroHeightWindowResidueSum f
        (h.height_schedule.height u) := by
        exact hfinite
    _ = explicitFormulaScheduledRectangleResidueSum f F.toContourFamily h u := by
        rfl

/-- The scheduled horizontal-side contribution of the rectangle. -/
noncomputable def explicitFormulaScheduledHorizontalSideDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- The scheduled full vertical-side contribution of the rectangle. -/
noncomputable def explicitFormulaScheduledCompletedVerticalSideDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaLeftLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- The scheduled rectangle integral decomposes into vertical and horizontal sides. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaScheduledRectangleContourIntegral f F h u =
      explicitFormulaScheduledCompletedVerticalSideDifference f F h u +
        explicitFormulaScheduledHorizontalSideDifference f F h u := by
  let r : ExplicitFormulaRectangle := F.rectangle (h.height_schedule.height u)
  calc
    explicitFormulaScheduledRectangleContourIntegral f F h u =
        zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r +
          zetaCompletedExplicitFormulaTopLineIntegral f r -
          zetaCompletedExplicitFormulaBottomLineIntegral f r := by
      exact zetaCompletedExplicitFormulaContourIntegral_eq f r
    _ =
        (zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r) +
          (zetaCompletedExplicitFormulaTopLineIntegral f r -
            zetaCompletedExplicitFormulaBottomLineIntegral f r) := by
      let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f r
      let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f r
      let T : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f r
      let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f r
      calc
        R - L + T - B = (R - L + T) + -B := by
          exact sub_eq_add_neg (R - L + T) B
        _ = (R - L) + T + -B := rfl
        _ = (R - L) + (T + -B) := by
          exact add_assoc (R - L) T (-B)
        _ = (R - L) + (T - B) := by
          exact congrArg (fun x : ℂ => (R - L) + x)
            (sub_eq_add_neg T B).symm
    _ =
        explicitFormulaScheduledCompletedVerticalSideDifference f F h u +
          explicitFormulaScheduledHorizontalSideDifference f F h u := rfl

/-- The horizontal-side decay target along the selected schedule.

This is the horizontal estimate in the contour-integral-to-boundary path; it is
recorded as a named step consumed by the selected-channel convergence primitive. -/
def explicitFormulaScheduledHorizontalSideDifferenceTendstoZero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) : Prop :=
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledHorizontalSideDifference f F.toContourFamily h u)
      atTop
      (𝓝 0)

/-- The selected scheduled vertical contour realization. -/
noncomputable def explicitFormulaSelectedScheduledVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionIntegral
    f F (h.height_schedule.height u) channel

/-- The selected boundary channel contribution. -/
noncomputable def explicitFormulaSelectedVerticalBoundaryChannel
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledVerticalChannelProjectionContribution f channel

/-- The selected projected decomposition error is the finite selected channel minus its
limiting boundary channel. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_eq_selectedChannel_sub_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel =
      explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
        explicitFormulaSelectedVerticalBoundaryChannel f channel := by
  rfl

/-- The selected finite channel is exactly the scheduled projection integral. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_eq_projectionIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaSelectedScheduledVerticalChannel f F h u channel =
      explicitFormulaScheduledVerticalChannelProjectionIntegral
        f F (h.height_schedule.height u) channel := by
  rfl

/-- The selected limiting channel is exactly the scheduled projection contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_eq_projectionContribution
    (f : ZetaAdmissibleFunction)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) :
    explicitFormulaSelectedVerticalBoundaryChannel f channel =
      explicitFormulaScheduledVerticalChannelProjectionContribution f channel := by
  rfl

/-- The selected prime finite channel is the concrete prime vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_prime_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected archimedean finite channel is the concrete archimedean vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected correction finite channel is the concrete correction vertical channel. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_correction_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionVerticalChannel
        f F (h.height_schedule.height u) := by
  rfl

/-- The selected prime boundary channel is the completed prime contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_prime_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.prime =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The selected archimedean boundary channel is the completed archimedean contribution. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  rfl

/-- The selected scheduled archimedean channel is its selected boundary
contribution plus the concrete archimedean transport remainder. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq_boundary_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
  calc
    explicitFormulaSelectedScheduledVerticalChannel
        f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) := by
      exact explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq f F h u
    _ =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
      exact
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u)
    _ =
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean +
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u) := by
      exact
        congrArg
          (fun z : ℂ =>
            z +
              zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
                f F (h.height_schedule.height u))
          (explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq f).symm

/-- The selected correction boundary channel is the standard-contour correction
boundary value. -/
theorem explicitFormulaSelectedVerticalBoundaryChannel_correction_eq
    (f : ZetaAdmissibleFunction) :
    explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.correction =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  rfl

/-! ## Vertical-channel algebraic transport roots -/

/-- Shared algebraic passage from a scheduled component transport remainder to the
corresponding boundary-channel convergence.

This lemma is deliberately conditional: the analytic convergence of the transport
remainder belongs to the contour assembly layer, after finite-rectangle residue
equality and horizontal decay have both been supplied. -/
theorem explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
    (contribution : ℂ)
    (remainder : ℝ → ℂ)
    (channel : ℝ → ℂ)
    (hchannel : ∀ u : ℝ, channel u = contribution + remainder u)
    (hremainder : Tendsto remainder atTop (𝓝 0)) :
    Tendsto channel atTop (𝓝 contribution) := by
  have hconst :
      Tendsto (fun _u : ℝ => contribution) atTop (𝓝 contribution) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ => contribution + remainder u)
        atTop
        (𝓝 (contribution + 0)) :=
    hconst.add hremainder
  have htarget :
      contribution + 0 = contribution :=
    add_zero contribution
  have hpointwise :
      channel = fun u : ℝ => contribution + remainder u := by
    funext u
    exact hchannel u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 contribution))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => contribution + remainder u) atTop (𝓝 z))
      htarget
      hsum)

/-- The selected projected error is the difference between a convergent selected finite
channel and its limiting boundary channel. -/
theorem explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_of_selectedChannel_tendsto_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel))) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _u : ℝ => explicitFormulaSelectedVerticalBoundaryChannel f channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel f channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel)) :=
    hchannel.sub hconst
  have hzero :
      explicitFormulaSelectedVerticalBoundaryChannel f channel -
        explicitFormulaSelectedVerticalBoundaryChannel f channel = 0 :=
    sub_self _
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel) =
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
            explicitFormulaSelectedVerticalBoundaryChannel f channel) := by
    funext u
    exact
      explicitFormulaScheduledProjectedVerticalDecompositionError_eq_selectedChannel_sub_boundary
        f F h u channel
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel f F h u channel -
              explicitFormulaSelectedVerticalBoundaryChannel f channel)
          atTop
          (𝓝 z))
      hzero
      hsub)

/-! ## Channel-specific transport owner surfaces -/

/-- A selected channel transport remainder vanishes once the scheduled selected channel
has been analytically identified with its limiting boundary contribution. -/
theorem explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel f F h u channel)
        atTop
        (𝓝 (explicitFormulaSelectedVerticalBoundaryChannel f channel))) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F (h.height_schedule.height u) channel)
      atTop
      (𝓝 0) := by
  have herror :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F h u channel)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledProjectedVerticalDecompositionError_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h channel hchannel
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
          f F (h.height_schedule.height u) channel) =
        (fun u : ℝ =>
          explicitFormulaScheduledProjectedVerticalDecompositionError
            f F h u channel) := by
    funext u
    exact
      (explicitFormulaScheduledProjectedVerticalDecompositionError_eq_transportRemainder
        f F h u channel).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    herror

/-- Owner analytic leaf: the prime logarithmic-derivative vertical-channel transport
remainder vanishes along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  sorry

/-- Selected prime-channel analytic transport: the scheduled selected prime channel
converges to its selected boundary contribution. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.prime)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      (fun u : ℝ =>
        calc
          explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime =
            zetaCompletedExplicitFormulaPrimeVerticalChannel
              f F (h.height_schedule.height u) := by
              exact explicitFormulaSelectedScheduledVerticalChannel_prime_eq f F h u
          _ =
            zetaCompletedExplicitFormulaPrimeContribution f +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F (h.height_schedule.height u) := by
              exact
                zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
                  f F (h.height_schedule.height u)
          _ =
            explicitFormulaSelectedVerticalBoundaryChannel
                f ExplicitFormulaScheduledVerticalChannelProjection.prime +
              zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                f F (h.height_schedule.height u) := by
              exact
                congrArg
                  (fun z : ℂ =>
                    z +
                      zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
                        f F (h.height_schedule.height u))
                  (explicitFormulaSelectedVerticalBoundaryChannel_prime_eq f).symm)
      (zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
        f F h)

/-- Concrete prime-channel analytic transport: the scheduled prime logarithmic-derivative
vertical integral converges to the completed prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  have hselected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.prime)) :=
    explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannel f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaSelectedScheduledVerticalChannel_prime_eq f F h u
  have htarget :
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime =
        zetaCompletedExplicitFormulaPrimeContribution f :=
    explicitFormulaSelectedVerticalBoundaryChannel_prime_eq f
  have hselectedConcreteTarget :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
          atTop
          (𝓝 z))
      htarget
      hselected
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)))
    hpointwise
    hselectedConcreteTarget

/-- Prime-channel analytic transport: the scheduled prime vertical integral converges to
the completed prime boundary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.prime)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.prime)) := by
  exact
    explicitFormulaSelectedScheduledVerticalChannel_prime_tendsto_boundary_ownerChannelTransportAnalytic
      f F h

/-- Owner analytic leaf: the archimedean Gamma/completion vertical-channel
transport remainder vanishes along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  sorry

/-- Selected archimedean-channel analytic transport: the scheduled selected
archimedean channel converges to its selected boundary contribution. -/
theorem explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (explicitFormulaSelectedVerticalBoundaryChannel
        f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq_boundary_add_transportRemainder
          f F h u)
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
        f F h)

/-- Concrete archimedean-channel analytic transport: the scheduled Gamma/completion
vertical integral converges to the completed archimedean contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hselected :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) :=
    explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
            (h.height_schedule.height u)) := by
    funext u
    exact explicitFormulaSelectedScheduledVerticalChannel_archimedean_eq f F h u
  have htarget :
      explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean =
        zetaCompletedExplicitFormulaArchimedeanContribution f :=
    explicitFormulaSelectedVerticalBoundaryChannel_archimedean_eq f
  have hselectedConcreteTarget :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaSelectedScheduledVerticalChannel
              f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
          atTop
          (𝓝 z))
      htarget
      hselected
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    hpointwise
    hselectedConcreteTarget

/-- Archimedean-channel analytic transport: the scheduled Gamma/completion vertical
integral converges to the completed archimedean boundary contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.archimedean)) := by
  exact
    explicitFormulaSelectedScheduledVerticalChannel_archimedean_tendsto_boundary_ownerChannelTransportAnalytic
      f F h

/-- Pointwise normalization of the correction vertical channel to the explicit two-pole
kernel.  The sign here is inherited from
`explicitFormulaCorrectionLogDerivative_eq_poleCorrection`; the left side is subtracted
with the same orientation convention as the other vertical channels. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_poleCorrectionVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  have hright :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
  have hleft :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
  exact congrArg₂ HSub.hSub
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hright)
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hleft)

/-- The corrected contribution is the centered two-pole coefficient applied to the
test transform at the basepoint. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_eq_centeredPolePhi
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution f =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f 0 := by
  exact zetaCompletedExplicitFormulaCorrectionContribution_eq f

/-- The right-face pole-correction vertical integral with the completed-pole kernel
written explicitly. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The left-face pole-correction vertical integral with the completed-pole kernel
written explicitly. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand of the right-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The `s = 1` summand of the right-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand of the left-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 1` summand of the left-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand on the top horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)

/-- The `s = 0` summand on the bottom horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)

/-- The `s = 1` summand on the top horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)

/-- The `s = 1` summand on the bottom horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)

/-- The right-face `s = 1` correction integrand is the isolated kernel evaluated
on the right path. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
  rfl

/-- The left-face `s = 1` correction integrand is the isolated kernel evaluated
on the left path. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
  rfl

/-- The top-edge `s = 1` correction integrand is the isolated kernel evaluated
on the top path. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) :=
  rfl

/-- The bottom-edge `s = 1` correction integrand is the isolated kernel evaluated
on the bottom path. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) :=
  rfl

/-- The tangent-weighted right-side integral is the old real-side integral
multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted left-side integral is the old real-side integral
multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted top side is definitionally the old top horizontal
integral, since the top parametrization has tangent `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T :=
  rfl

/-- The tangent-weighted bottom side is definitionally the old bottom horizontal
integral before the final boundary orientation sign is applied. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T :=
  rfl

/-- The genuine `s = 1` contour boundary unfolds to the old four real-side
integrals with the missing vertical tangent factors restored. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T := by
  let RT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T
  let LT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T
  let TT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T
  let BT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
  have hR : RT = R * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hL : LT = L * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hU : TT = U :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
      f F T
  have hB : BT = B :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        RT - LT + TT - BT := by
      rfl
    _ = R * Complex.I - LT + TT - BT := by
      exact congrArg (fun x : ℂ => x - LT + TT - BT) hR
    _ = R * Complex.I - L * Complex.I + TT - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - x + TT - BT) hL
    _ = R * Complex.I - L * Complex.I + U - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x - BT) hU
    _ = R * Complex.I - L * Complex.I + U - B := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + U - x) hB

/-- The isolated `s = 0` correction kernel as a function of the contour variable. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  (-1 / z) * zetaCompletedExplicitFormulaPhi f (z - 1 / 2)

/-- The tangent-weighted right side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted left side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted top side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)

/-- The tangent-weighted bottom side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)

/-- The genuine tangent-weighted rectangle contour integral for the isolated
`s = 0` correction kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T

/-- The tangent-weighted isolated `s = 0` rectangle boundary integral unfolds to
its four oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T :=
  rfl

/-- The right-face `s = 0` correction integrand is the isolated kernel evaluated
on the right path. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
  rfl

/-- The left-face `s = 0` correction integrand is the isolated kernel evaluated
on the left path. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
  rfl

/-- The top-edge `s = 0` correction integrand is the isolated kernel evaluated
on the top path. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) :=
  rfl

/-- The bottom-edge `s = 0` correction integrand is the isolated kernel evaluated
on the bottom path. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) :=
  rfl

/-- The tangent-weighted right-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted left-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted top `s = 0` side is definitionally the old top
horizontal integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The tangent-weighted bottom `s = 0` side is definitionally the old bottom
horizontal integral before the final boundary orientation sign is applied. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The genuine `s = 0` contour boundary unfolds to the old four real-side
integrals with the missing vertical tangent factors restored. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T := by
  let RT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let LT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let TT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T
  let BT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  have hR : RT = R * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hL : LT = L * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hU : TT = U :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_horizontal
      f F T
  have hB : BT = B :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_horizontal
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        RT - LT + TT - BT := by
      rfl
    _ = R * Complex.I - LT + TT - BT := by
      exact congrArg (fun x : ℂ => x - LT + TT - BT) hR
    _ = R * Complex.I - L * Complex.I + TT - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - x + TT - BT) hL
    _ = R * Complex.I - L * Complex.I + U - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x - BT) hU
    _ = R * Complex.I - L * Complex.I + U - B := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + U - x) hB

/-- The oriented finite-rectangle boundary integral for the `s = 0` correction pole. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T

/-- The oriented finite-rectangle boundary integral for the `s = 1` correction pole. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T

/-- The `s = 0` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The `s = 1` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T :=
  rfl

/-- The scheduled `s = 0` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
              f F (h.height_schedule.height u) :=
  rfl

/-- The scheduled `s = 1` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) :=
  rfl

/-- Additive algebra for isolating the left side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    L = R + H - C := by
  have hsum : L + C = R + H := by
    calc
      L + C = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + x) hC
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L)
      _ = (L + (R + -L)) + H := by
        exact (add_assoc L (R + -L) H).symm
      _ = ((L + R) + -L) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc L R (-L))
      _ = ((R + L) + -L) + H := by
        exact congrArg (fun x : ℂ => (x + -L) + H) (add_comm L R)
      _ = (R + (L + -L)) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc R L (-L)).symm
      _ = (R + 0) + H := by
        exact congrArg (fun x : ℂ => (R + x) + H) (add_right_neg L)
      _ = R + H := by
        exact congrArg (fun x : ℂ => x + H) (add_zero R)
  exact
    (eq_sub_iff_add_eq.mpr hsum).symm

/-- Additive algebra for isolating the right side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    R = L - H + C := by
  have hsum : R + H = C + L := by
    calc
      R + H = R + (L + -L + H) := by
        exact congrArg (fun x : ℂ => R + (x + H)) (add_right_neg L).symm
      _ = R + (L + (-L + H)) := by
        exact congrArg (fun x : ℂ => R + x) (add_assoc L (-L) H)
      _ = (R + L) + (-L + H) := by
        exact (add_assoc R L (-L + H)).symm
      _ = (L + R) + (-L + H) := by
        exact congrArg (fun x : ℂ => x + (-L + H)) (add_comm R L)
      _ = L + (R + (-L + H)) := by
        exact add_assoc L R (-L + H)
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + x) (add_assoc R (-L) H).symm
      _ = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L).symm
      _ = L + C := by
        exact congrArg (fun x : ℂ => L + x) hC.symm
      _ = C + L := by
        exact add_comm L C
  have hright : R = C + L - H := by
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  calc
    R = C + L - H := by
      exact hright
    _ = (C + L) + -H := by
      exact sub_eq_add_neg (C + L) H
    _ = (L + C) + -H := by
      exact congrArg (fun x : ℂ => x + -H) (add_comm C L)
    _ = L + (C + -H) := by
      exact add_assoc L C (-H)
    _ = L + (-H + C) := by
      exact congrArg (fun x : ℂ => L + x) (add_comm C (-H))
    _ = (L + -H) + C := by
      exact (add_assoc L (-H) C).symm
    _ = L - H + C := by
      exact congrArg (fun x : ℂ => x + C) (sub_eq_add_neg L H).symm

/-- The right vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  have hpos : 0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    Eq.symm hre ▸ F.c_pos
  exact fun hzero =>
    have hre_zero : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    (ne_of_gt hpos) hre_zero

/-- The right vertical side lies strictly to the right of the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  exact Eq.symm hre ▸ F.c_gt_one

/-- The right vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 ≠ 0 := by
  have hgt :
      1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one F T t
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaRightPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_gt hgt) hre_one

/-- The left vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t ≠ 0 := by
  exact fun hzero =>
    have hre :
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
          1 - F.c :=
      zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
    have hre_zero : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    have hsub_zero : 1 - F.c = 0 :=
      hre.symm.trans hre_zero
    have hc_one : F.c = 1 :=
      (sub_eq_zero.mp hsub_zero).symm
    F.c_ne_one hc_one

/-- The left vertical side lies strictly to the left of the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hleft : 1 - F.c < 0 :=
    F.one_sub_c_neg
  exact Eq.symm hre ▸ hleft

/-- On the left vertical face, the absolute real coordinate is the fixed
distance from the `s = 0` pole to the line. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    |(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re| =
      F.c - 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hre : z.re = 1 - F.c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hneg : z.re < 0 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero F T t
  have habs : |z.re| = -z.re :=
    abs_of_neg hneg
  have hneg_re : -z.re = F.c - 1 := by
    calc
      -z.re = -(1 - F.c) := by
        exact congrArg Neg.neg hre
      _ = F.c - 1 := by
        exact neg_sub 1 F.c
  exact Eq.trans habs hneg_re

/-- The left vertical face stays at least `F.c - 1` away from the `s = 0`
correction pole in norm. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    F.c - 1 ≤ ‖zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have habs_re :
      |z.re| = F.c - 1 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one F T t
  have hle_abs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hle_abs_target : F.c - 1 ≤ Complex.abs z :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs z)
      habs_re
      hle_abs
  have habs_norm : Complex.abs z = ‖z‖ :=
    (Complex.norm_eq_abs z).symm
  exact Eq.subst
    (motive := fun x : ℝ => F.c - 1 ≤ x)
    habs_norm
    hle_abs_target

/-- The isolated `s = 0` correction coefficient is uniformly bounded on the
left vertical face by the reciprocal of the line's distance from the pole. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖
      ≤ 1 / (F.c - 1) := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hpos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hle_norm : F.c - 1 ≤ ‖z‖ :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm F T t
  have hrecip : 1 / ‖z‖ ≤ 1 / (F.c - 1) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hneg_div : -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
    norm_neg (1 / z)
  have hnorm_div : ‖(1 : ℂ) / z‖ = ‖(1 : ℂ)‖ / ‖z‖ :=
    norm_div (1 : ℂ) z
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖-(1 / z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hneg_div
      _ = ‖1 / z‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / z‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact hnorm_div
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (F.c - 1))
    hcoeff.symm
    hrecip

/-- The shifted left vertical face lies in the fixed real strip used for the
completed transform estimates. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    min F.c (1 - F.c) - 1 / 2
        ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
        ≤ max F.c (1 - F.c) - 1 / 2 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
        (1 - F.c) - 1 / 2 := by
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re -
            (1 / 2 : ℂ).re := by
        exact Complex.sub_re
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = (1 - F.c) - (1 / 2 : ℂ).re := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).re)
          (zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t)
      _ = (1 - F.c) - 1 / 2 := by
        exact congrArg (fun x : ℝ => (1 - F.c) - x) Complex.ofReal_re
  constructor
  · have hmin : min F.c (1 - F.c) ≤ 1 - F.c :=
      min_le_right F.c (1 - F.c)
    have hsub : min F.c (1 - F.c) - 1 / 2 ≤ (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmin (1 / 2)
    exact Eq.symm hre ▸ hsub
  · have hmax : 1 - F.c ≤ max F.c (1 - F.c) :=
      le_max_right F.c (1 - F.c)
    have hsub : (1 - F.c) - 1 / 2 ≤ max F.c (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmax (1 / 2)
    exact Eq.symm hre ▸ hsub

/-- The shifted left vertical face has imaginary coordinate norm `‖t‖`. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_im_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im‖ =
      ‖t‖ := by
  have him :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im = t := by
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).im -
            (1 / 2 : ℂ).im := by
        exact Complex.sub_im
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = t - (1 / 2 : ℂ).im := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).im)
          (zetaCompletedExplicitFormulaLeftPath_im (F.rectangle T) t)
      _ = t - 0 := by
        exact congrArg (fun x : ℝ => t - x) Complex.ofReal_im
      _ = t := by
        exact sub_zero t
  exact congrArg (fun x : ℝ => ‖x‖) him

/-- Pointwise decay for the left-face isolated `s = 0` correction integrand.

This is the genuine denominator-separation part of the all-height Cauchy
estimate; the remaining finite-window theorem must convert this vertical-line
oscillatory decay into the rectangle cancellation bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_norm_le_phiDecay
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T t : ℝ) (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
      ≤
        (1 / (F.c - 1)) *
          (hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have ha :
      ‖a‖ ≤ 1 / (F.c - 1) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
  have hb :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t))
  have hA_nonneg : 0 ≤ 1 / (F.c - 1) :=
    le_of_lt (div_pos zero_lt_one (sub_pos.mpr F.c_gt_one))
  have hproduct :
      ‖a * b‖
        ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
        exact mul_le_mul ha hb (norm_nonneg b) hA_nonneg
  exact hproduct

/-- IBP-backed uniform rapid decay for the left-face isolated `s = 0`
correction integrand.

The denominator is separated from the pole by the fixed distance `F.c - 1`;
the transform decay comes from the Paley-Wiener vertical integration-by-parts
owner theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_uniformRapidDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ T t : ℝ,
        ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
          ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
  match
    zetaPhi_verticalStripRapidDecay_of_admissible_owner
      f
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      N with
  | ⟨Cφ, hCφpos, hCφ⟩ =>
      let K : ℝ := 1 / (F.c - 1)
      have hKpos : 0 < K :=
        div_pos zero_lt_one (sub_pos.mpr F.c_gt_one)
      refine ⟨K * Cφ, mul_pos hKpos hCφpos, ?_⟩
      intro T t
      let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2
      let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
      let b : ℂ := zetaCompletedExplicitFormulaPhi f z
      have hcoeff : ‖a‖ ≤ K :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
      have hstrip :
          min F.c (1 - F.c) - 1 / 2 ≤ z.re ∧
            z.re ≤ max F.c (1 - F.c) - 1 / 2 :=
        zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
      have hphi_raw :
          ‖b‖ ≤ Cφ * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
        hCφ z hstrip.1 hstrip.2
      have him_norm :
          ‖z.im‖ = ‖t‖ :=
        zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t
      have hphi :
          ‖b‖ ≤ Cφ * (1 + ‖t‖) ^ (-(N : ℤ)) :=
        Eq.subst
          (motive := fun u : ℝ => ‖b‖ ≤ Cφ * (1 + u) ^ (-(N : ℤ)))
          him_norm
          hphi_raw
      have hK_nonneg : 0 ≤ K :=
        le_of_lt hKpos
      have hprod :
          ‖a * b‖ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
        calc
          ‖a * b‖ = ‖a‖ * ‖b‖ := by
            exact norm_mul a b
          _ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
            exact mul_le_mul hcoeff hphi (norm_nonneg b) hK_nonneg
      have hassoc :
          K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) =
            (K * Cφ) * (1 + ‖t‖) ^ (-(N : ℤ)) :=
        (mul_assoc K Cφ ((1 + ‖t‖) ^ (-(N : ℤ)))).symm
      exact le_trans hprod (le_of_eq hassoc)

/-- The left vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hlt : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 1 := by
    have hpos : 0 < (F.rectangle T).c :=
      F.c_pos
    exact Eq.symm hre ▸ sub_lt_self (1 : ℝ) hpos
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_lt hlt) hre_one

/-- The shifted completed transform is continuous along the right vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- The shifted completed transform is continuous along the left vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- Right vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaRightPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inl ⟨t, ht, rfl⟩
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Left vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Right vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Left vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Fixed-height reconstruction of the inverse-Gamma completion channel from the
archimedean packet and the pole-correction packet. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T := by
  let S : Set ℝ := Set.Icc (-(F.rectangle T).T) (F.rectangle T).T
  let RA : ℂ :=
    ∫ t in S,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let RC : ℂ :=
    ∫ t in S,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)
  let LA : ℂ :=
    ∫ t in S,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  let LC : ℂ :=
    ∫ t in S,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have hRA :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn
      f hPhi F T havoid
  have hRC :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn
      f hPhi F T
  have hLA :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn
      f hPhi F T havoid
  have hLC :
      IntegrableOn
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        S :=
    zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn
      f hPhi F T
  have hrightAdd :
      (∫ t in S,
        explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        RA + RC := by
    exact integral_add hRA hRC
  have hleftAdd :
      (∫ t in S,
        explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        LA + LC := by
    exact integral_add hLA hLC
  have hrightInv :
      (∫ t in S,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        RA + RC := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaArchimedean_rightIntegral_add_correction_integrand_eq_inverseGammaCompletion
        f F T).symm
      hrightAdd
  have hleftInv :
      (∫ t in S,
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        LA + LC := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaArchimedean_leftIntegral_add_correction_integrand_eq_inverseGammaCompletion
        f F T).symm
      hleftAdd
  calc
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T =
        (RA + RC) - (LA + LC) := by
      exact congrArg₂ Sub.sub hrightInv hleftInv
    _ = (RA - LA) + (RC - LC) := by
      exact add_sub_add_comm RA RC LA LC
    _ =
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T := by
      rfl

/-- Local integrability of the right-face `s = 0` correction-pole summand on a
finite scheduled height interval. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcoeff :
      Continuous
        (fun t : ℝ =>
          -1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    exact continuous_const.div hpath
      (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero F T t)
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous f hPhi F T
  exact (hcoeff.mul hphi).integrableOn_Icc

/-- Local integrability of the right-face `s = 1` correction-pole summand on a
finite scheduled height interval. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hden :
      Continuous
        (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    exact hpath.sub continuous_const
  have hcoeff :
      Continuous
        (fun t : ℝ =>
          -1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) := by
    exact continuous_const.div hden
      (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero F T t)
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous f hPhi F T
  exact (hcoeff.mul hphi).integrableOn_Icc

/-- Algebraic splitting of the two-pole correction coefficient after
multiplication by a common test value. -/
theorem correctionPoleCoefficient_mul_split (s φ : ℂ) :
    (-1 / s - 1 / (s - 1)) * φ =
      (-1 / s) * φ + (-1 / (s - 1)) * φ := by
  have hsub :
      (-1 / s - 1 / (s - 1)) * φ =
        (-1 / s) * φ - (1 / (s - 1)) * φ :=
    sub_mul (-1 / s) (1 / (s - 1)) φ
  have hsub_add :
      (-1 / s) * φ - (1 / (s - 1)) * φ =
        (-1 / s) * φ + (-((1 / (s - 1)) * φ)) :=
    sub_eq_add_neg ((-1 / s) * φ) ((1 / (s - 1)) * φ)
  have hneg_mul :
      -((1 / (s - 1)) * φ) = (-(1 / (s - 1))) * φ :=
    (neg_mul (1 / (s - 1)) φ).symm
  have hneg_coeff :
      -(1 / (s - 1)) = -1 / (s - 1) :=
    (neg_div (s - 1) (1 : ℂ)).symm
  have hneg_term :
      -(1 / (s - 1)) * φ = (-1 / (s - 1)) * φ :=
    congrArg (fun c : ℂ => c * φ) hneg_coeff
  have htail :
      -(1 / (s - 1) * φ) = (-1 / (s - 1)) * φ :=
    Eq.trans hneg_mul hneg_term
  exact
    Eq.trans hsub
      (Eq.trans hsub_add
        (congrArg (fun ψ : ℂ => (-1 / s) * φ + ψ) htail))

/-- Pointwise algebra splitting the right-face two-pole correction kernel after
multiplication by the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegrand_eq_zero_add_one
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
        (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
  exact
    correctionPoleCoefficient_mul_split
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)
      (zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))

/-- Local integrability of the left-face `s = 0` correction-pole summand on a
finite scheduled height interval. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcoeff :
      Continuous
        (fun t : ℝ =>
          -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    exact continuous_const.div hpath
      (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero F T t)
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous f hPhi F T
  exact (hcoeff.mul hphi).integrableOn_Icc

/-- Local integrability of the left-face `s = 1` correction-pole summand on a
finite scheduled height interval. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hden :
      Continuous
        (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    exact hpath.sub continuous_const
  have hcoeff :
      Continuous
        (fun t : ℝ =>
          -1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) := by
    exact continuous_const.div hden
      (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero F T t)
  have hphi :
      Continuous
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
    zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous f hPhi F T
  exact (hcoeff.mul hphi).integrableOn_Icc

/-- Pointwise algebra splitting the left-face two-pole correction kernel after
multiplication by the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegrand_eq_zero_add_one
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
        (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  exact
    correctionPoleCoefficient_mul_split
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
      (zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))

/-- The right pole-correction integral is the sum of its two one-pole summands.

This is the local set-integral accounting step; the analytic content is isolated in
the two one-pole limit theorems below. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_eq_zero_add_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T := by
  have hzero :
      IntegrableOn
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegrableOn f hPhi F T
  have hone :
      IntegrableOn
        (fun t : ℝ =>
          (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrableOn f hPhi F T
  have hpoint :
      (fun t : ℝ =>
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegrand_eq_zero_add_one
        f F T t
  have hintegral_point :
      zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral f F T =
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) :=
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hpoint
  have hadd :
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T := by
    exact integral_add hzero hone
  exact Eq.trans hintegral_point hadd

/-- The left pole-correction integral is the sum of its two one-pole summands. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_eq_zero_add_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T := by
  have hzero :
      IntegrableOn
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrableOn f hPhi F T
  have hone :
      IntegrableOn
        (fun t : ℝ =>
          (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrableOn f hPhi F T
  have hpoint :
      (fun t : ℝ =>
        (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegrand_eq_zero_add_one
        f F T t
  have hintegral_point :
      zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral f F T =
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) :=
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hpoint
  have hadd :
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) +
            (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T := by
    exact integral_add hzero hone
  exact Eq.trans hintegral_point hadd

/-- The scheduled rectangles eventually enclose the right-face `s = 0`
single-pole residue point. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_eventually_mem_interior
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_zero_mem_interior

/-- The scheduled rectangles eventually enclose the left-face `s = 1`
single-pole residue point. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePole_eventually_mem_interior
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈
        explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
  h.eventually_one_mem_interior

/-- The right face stays strictly to the right of the enclosed `s = 0` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    0 < (zetaCompletedExplicitFormulaRightPath
      (F.rectangle (hSchedule.height u)) t).re := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath
        (F.rectangle (hSchedule.height u)) t).re =
        (F.rectangle (hSchedule.height u)).c :=
    zetaCompletedExplicitFormulaRightPath_re
      (F.rectangle (hSchedule.height u)) t
  exact Eq.symm hre ▸ F.c_pos

/-- The right face stays strictly to the right of the enclosed `s = 1` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    1 < (zetaCompletedExplicitFormulaRightPath
      (F.rectangle (hSchedule.height u)) t).re :=
  zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one
    F (hSchedule.height u) t

/-- The left face stays strictly to the left of the enclosed `s = 0` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
      (F.rectangle (hSchedule.height u)) t).re < 0 :=
  zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero
    F (hSchedule.height u) t

/-- The left face stays strictly to the left of the enclosed `s = 1` pole along
the scheduled rectangles. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePole_scheduledFaceSeparates
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath
      (F.rectangle (hSchedule.height u)) t).re < 1 := by
  have hlt_zero :
      (zetaCompletedExplicitFormulaLeftPath
        (F.rectangle (hSchedule.height u)) t).re < 0 :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledFaceSeparates
      F hSchedule u t
  exact lt_trans hlt_zero zero_lt_one

/-- Scheduled top horizontal points never hit the `s = 1` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePole_scheduledPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ) :
    zetaCompletedExplicitFormulaTopPath
        (F.rectangle (hSchedule.height u)) x - 1 ≠ 0 := by
  intro hzero
  have hpath_eq_one :
      zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x = 1 :=
    sub_eq_zero.mp hzero
  have him_one :
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x).im = (1 : ℂ).im :=
    congrArg Complex.im hpath_eq_one
  have him_height :
      (zetaCompletedExplicitFormulaTopPath
          (F.rectangle (hSchedule.height u)) x).im =
        hSchedule.height u :=
    zetaCompletedExplicitFormulaTopPath_im
      (F.rectangle (hSchedule.height u)) x
  have hone_im : (1 : ℂ).im = (0 : ℝ) :=
    Complex.one_im
  have hheight_zero : hSchedule.height u = 0 :=
    Eq.trans him_height.symm (Eq.trans him_one hone_im)
  exact hSchedule.height_ne_zero u hheight_zero

/-- Scheduled bottom horizontal points never hit the `s = 1` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePole_scheduledPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (u x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath
        (F.rectangle (hSchedule.height u)) x - 1 ≠ 0 := by
  intro hzero
  have hpath_eq_one :
      zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x = 1 :=
    sub_eq_zero.mp hzero
  have him_one :
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x).im = (1 : ℂ).im :=
    congrArg Complex.im hpath_eq_one
  have him_height :
      (zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (hSchedule.height u)) x).im =
        -hSchedule.height u :=
    zetaCompletedExplicitFormulaBottomPath_im
      (F.rectangle (hSchedule.height u)) x
  have hone_im : (1 : ℂ).im = (0 : ℝ) :=
    Complex.one_im
  have hneg_height_zero : -hSchedule.height u = 0 :=
    Eq.trans him_height.symm (Eq.trans him_one hone_im)
  have hheight_zero : hSchedule.height u = 0 :=
    neg_eq_zero.mp hneg_height_zero
  exact hSchedule.height_ne_zero u hheight_zero

/-- Algebraic residue cancellation for the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
    (z φ : ℂ) (hz : z ≠ 0) :
    z * ((-1 / z) * φ) = -φ := by
  have hdiv_neg :
      -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hcoeff :
      z * (-1 / z) = -1 := by
    calc
      z * (-1 / z) =
          z * (-(1 / z)) := by
        exact congrArg (fun a : ℂ => z * a) hdiv_neg
      _ = -(z * (1 / z)) := by
        exact (mul_neg z (1 / z)).symm
      _ = -(z * z⁻¹) := by
        have hone_div : 1 / z = z⁻¹ := by
          exact one_div z
        exact congrArg (fun a : ℂ => -(z * a)) hone_div
      _ = -1 := by
        exact congrArg Neg.neg (mul_inv_cancel₀ hz)
  calc
    z * ((-1 / z) * φ) =
        (z * (-1 / z)) * φ := by
      exact (mul_assoc z (-1 / z) φ).symm
    _ = (-1) * φ := by
      exact congrArg (fun a : ℂ => a * φ) hcoeff
    _ = -φ := by
      exact neg_one_mul φ

/-- Local residue of the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  have hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) := by
    have hcontinuous :
        ContinuousAt
          (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (0 : ℂ) :=
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi (0 : ℂ)).continuousAt
    exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have htarget_arg : (0 : ℂ) - 1 / 2 = -(1 / 2 : ℂ) := by
    exact zero_sub (1 / 2 : ℂ)
  have hneg :
      Tendsto
        (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hphi.neg
  have hpointwise :
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2))) =
       ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) := by
    exact
      self_mem_nhdsWithin.mono
        (fun z hz_ne =>
          zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
            z
            (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
            hz_ne)
  have hraw :
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hpointwise.tendsto_iff.2 hneg
  exact Eq.subst
    (motive := fun w : ℂ =>
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f w)))
    htarget_arg
    hraw

/-- The isolated `s = 0` correction kernel is differentiable away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z := by
  have hcoeff :
      DifferentiableAt ℂ (fun w : ℂ => -1 / w) z :=
    (differentiableAt_const (-(1 : ℂ))).div differentiableAt_id hz
  have hshift :
      DifferentiableAt ℂ
        (fun w : ℂ => zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z :=
    zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi z
  exact hcoeff.mul hshift

/-- The isolated `s = 0` correction kernel is continuous away from its pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      z :=
  (zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole
    f hPhi hz).continuousAt

/-- Boundary avoidance excludes the isolated `s = 0` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_ne_of_avoidsBoundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    z ≠ 0 := by
  intro hz
  have hsingular : explicitFormulaContourSingularPoint z :=
    Or.inl hz
  exact havoid z hsingular hboundary

/-- The isolated `s = 0` correction kernel is regular at every avoided boundary point. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ) {z : ℂ}
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hboundary : z ∈ explicitFormulaContourFamilyBoundary F T) :
    ContinuousAt
        (fun w : ℂ =>
          (-1 / w) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z ∧
      DifferentiableAt ℂ
        (fun w : ℂ =>
          (-1 / w) *
            zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
        z := by
  have hz :
      z ≠ 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_ne_of_avoidsBoundary
      F T havoid hboundary
  exact And.intro
    (zetaCompletedExplicitFormulaCorrectionZeroPole_continuousAt_off_pole f hPhi hz)
    (zetaCompletedExplicitFormulaCorrectionZeroPole_differentiableAt_off_pole f hPhi hz)

/-- The isolated `s = 0` correction kernel is regular at every boundary point of
an avoided rectangle. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  fun _ hz =>
    zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_boundary_of_avoidsBoundary
      f F hPhi T havoid hz

/-- The scheduled rectangles supply boundary regularity for the isolated `s = 0`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / w) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The isolated `s = 0` correction kernel is continuous on every avoided rectangle
boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_continuousOn_boundary_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F T) := by
  intro z hz
  exact
    (zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid z hz).1.continuousWithinAt

/-- The scheduled rectangles supply boundary continuity for the isolated `s = 0`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / w) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- Positive-height residue inputs for the isolated `s = 0` correction kernel:
the pole is inside the rectangle, the kernel is regular on the avoided boundary,
and the local residue is the already computed zero-pole residue. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_tangentResidueInputs_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T ∧
      (∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z) ∧
      Tendsto
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  have hinterior :
      (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F T :=
    explicitFormulaContourFamilyInterior_zero_mem F T hT
  have hregular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z ∧
            DifferentiableAt ℂ
              (fun w : ℂ =>
                zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
              z :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_regularAt_all_boundary_points_of_avoidsBoundary
      f F hPhi T havoid
  have hlocal :
      Tendsto
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
      f hPhi
  exact And.intro hinterior (And.intro hregular hlocal)

/-- Scheduled residue inputs for the isolated `s = 0` correction kernel at
eventually positive heights. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentResidueInputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (0 : ℂ) ∈ explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
        (∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
                z ∧
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f w)
                z) ∧
        Tendsto
          (fun z : ℂ =>
            z *
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
          (𝓝[≠] (0 : ℂ))
          (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPole_tangentResidueInputs_of_pos_height
        f F h.phi_control (h.height_schedule.height u) hu
        (h.height_schedule.avoids_boundary u))

/-- The normalized local residue value for the isolated `s = 0` correction
kernel.  This is the residue value that any finite single-pole rectangle theorem
for `zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral`
must return in the project normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueValue
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) =
      -zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) := by
  exact congrArg (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f z)
    (zero_sub (1 / 2 : ℂ)).symm

/-- The local residue target written at the literal pole coordinate is the same
as the corrected project-normalized residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueCoordinateTarget_eq_projectTarget
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) =
      -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) :=
  (zetaCompletedExplicitFormulaCorrectionZeroPole_localResidueValue f).symm

/-- The normalized local residue value for the isolated `s = 1` correction
kernel, written at the literal pole coordinate. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidueValue
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f (1 / 2) =
      -zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) := by
  exact congrArg (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f z)
    (sub_half (1 : ℂ)).symm

/-- The local residue target written at the literal one-pole coordinate is the
same as the project-normalized `s = 1` residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_localResidueCoordinateTarget_eq_projectTarget
    (f : ZetaAdmissibleFunction) :
    -zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) =
      -zetaCompletedExplicitFormulaPhi f (1 / 2) :=
  (zetaCompletedExplicitFormulaCorrectionOnePole_localResidueValue f).symm

/-- In the pole-enclosing geometry, the unordered horizontal span is the
left-to-right closed interval used by a standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc
    (F : ExplicitFormulaContourFamily) :
    Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c := by
  have hleft_le_right : 1 - F.c ≤ F.c :=
    le_of_lt
      (lt_trans F.one_sub_c_neg F.c_pos)
  exact Set.uIcc_of_ge hleft_le_right

/-- The top tangent edge of the isolated `s = 0` correction contour can be read
over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc F)

/-- The bottom tangent edge of the isolated `s = 0` correction contour can be
read over the left-to-right horizontal interval. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T =
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) := by
  exact congrArg
    (fun s : Set ℝ =>
      ∫ x in s,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x))
    (zetaCompletedExplicitFormulaCorrectionPoleHorizontal_uIcc_eq_Icc F)

/-- The isolated `s = 0` tangent rectangle boundary with the horizontal sides
written in left-to-right rectangle coordinates. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_IccHorizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
          (∫ x in Set.Icc (1 - F.c) F.c,
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
              (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) -
            (∫ x in Set.Icc (1 - F.c) F.c,
              zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
                (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) := by
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T
  let B : ℂ := zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T
  let U' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  let B' : ℂ :=
    ∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  have hU : U = U' :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_Icc
      f F T
  have hB : B = B' :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_Icc
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        R - L + U - B := by
      rfl
    _ = R - L + U' - B := by
      exact congrArg (fun x : ℂ => R - L + x - B) hU
    _ = R - L + U' - B' := by
      exact congrArg (fun x : ℂ => R - L + U' - x) hB

/-- The standard positively oriented rectangle boundary expression for the
isolated `s = 0` kernel, in Mathlib's rectangle-Cauchy convention. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ x in Set.Icc (1 - F.c) F.c,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T

/-- The standard rectangle boundary expression unfolds to Mathlib's
bottom-minus-top plus right-minus-left tangent convention. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T =
      (∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
        (∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T :=
  rfl

/-- The project-normalized standard rectangle boundary for the isolated
`s = 0` kernel.  The raw positively oriented contour has the usual `2πi`
factor; this object is the one whose finite Cauchy residue value is the local
residue itself. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T

/-- The normalized standard rectangle boundary unfolds to `(2πi)⁻¹` times the
raw standard contour boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F T :=
  rfl

/-- Transport from the raw standard finite Cauchy theorem, with its `2πi`
factor, to the project-normalized residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hraw :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
      -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let R : ℂ := -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))
  have hnorm :
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
          f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T := by
    rfl
  have hraw' :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T = C * R :=
    hraw
  have hC_ne : C ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (show (2 : ℝ) ≠ 0 from two_ne_zero))
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F T =
        C⁻¹ *
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T := hnorm
    _ = C⁻¹ * (C * R) := by
      exact congrArg (fun z : ℂ => C⁻¹ * z) hraw'
    _ = (C⁻¹ * C) * R := by
      exact (mul_assoc C⁻¹ C R).symm
    _ = 1 * R := by
      exact congrArg (fun z : ℂ => z * R) (inv_mul_cancel₀ hC_ne)
    _ = R := by
      exact one_mul R

/-- The exact orientation defect between the project's tangent side convention
and the standard positively oriented rectangle boundary. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T

/-- The project tangent boundary is the standard rectangle-Cauchy boundary plus
the explicit orientation defect. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T := by
  let P : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T
  have hsum : S + (P - S) = P := by
    calc
      S + (P - S) = (P - S) + S := by
        exact add_comm S (P - S)
      _ = P := by
        exact sub_add_cancel P S
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T = P := by
      rfl
    _ = S + (P - S) := by
      exact hsum.symm
    _ =
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T := by
      rfl

/-- Scheduled form of the project/standard tangent-boundary orientation
decomposition for the isolated `s = 0` kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u) :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_standard_add_orientationDefect
    f F (h.height_schedule.height u)

/-- Additive algebra for the project/standard horizontal orientation defect. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_orientationDefect_horizontal_algebra
    (A H : ℂ) :
    (A + H) - (A - H) = H + H := by
  have hsum :
      (A - H) + (H + H) = A + H := by
    calc
      (A - H) + (H + H) = (A + -H) + (H + H) := by
        exact congrArg (fun x : ℂ => x + (H + H)) (sub_eq_add_neg A H)
      _ = A + (-H + (H + H)) := by
        exact add_assoc A (-H) (H + H)
      _ = A + ((-H + H) + H) := by
        exact congrArg (fun x : ℂ => A + x) (add_assoc (-H) H H).symm
      _ = A + (0 + H) := by
        exact congrArg (fun x : ℂ => A + (x + H)) (neg_add_cancel H)
      _ = A + H := by
        exact congrArg (fun x : ℂ => A + x) (zero_add H)
  exact eq_sub_of_add_eq' hsum

/-- Additive algebra putting the standard rectangle horizontal convention in
`right-minus-left` plus negative horizontal-remainder form. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_standardBoundary_horizontal_algebra
    (R L U B : ℂ) :
    B - U + R - L = R - L - (U - B) := by
  calc
    B - U + R - L = (B + -U) + R - L := by
      exact congrArg (fun x : ℂ => x + R - L) (sub_eq_add_neg B U)
    _ = R + (B + -U) - L := by
      exact congrArg (fun x : ℂ => x - L) (add_comm (B + -U) R)
    _ = R + (B - U) - L := by
      exact congrArg (fun x : ℂ => R + x - L) (sub_eq_add_neg B U).symm
    _ = R + (B - U + -L) := by
      exact sub_eq_add_neg (R + (B - U)) L
    _ = R + (-L + (B - U)) := by
      exact congrArg (fun x : ℂ => R + x) (add_comm (B - U) (-L))
    _ = R + -L + (B - U) := by
      exact (add_assoc R (-L) (B - U)).symm
    _ = R - L + (B - U) := by
      exact congrArg (fun x : ℂ => x + (B - U)) (sub_eq_add_neg R L).symm
    _ = R - L + -(U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (neg_sub U B).symm
    _ = R - L - (U - B) := by
      exact (sub_eq_add_neg (R - L) (U - B)).symm

/-- The scheduled project/standard orientation defect is exactly two copies of
the scheduled horizontal zero-pole remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ := zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  let P : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T
  let S : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T
  let H : ℂ := zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u
  have hP : P = R - L + U - B :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hS : S = B - U + R - L := by
    rfl
  have hH : H = U - B := by
    rfl
  let A : ℂ := R - L
  have hP_AH : P = A + H := by
    calc
      P = R - L + U - B := hP
      _ = (R - L) + (U - B) := by
        exact (add_sub_assoc (R - L) U B).symm
      _ = A + (U - B) := by
        rfl
      _ = A + H := by
        exact congrArg (fun x : ℂ => A + x) hH.symm
  have hS_AH : S = A - H := by
    calc
      S = B - U + R - L := hS
      _ = R - L - (U - B) := by
        exact
          zetaCompletedExplicitFormulaCorrectionZeroPole_standardBoundary_horizontal_algebra
            R L U B
      _ = A - (U - B) := by
        rfl
      _ = A - H := by
        exact congrArg (fun x : ℂ => A - x) hH.symm
  have hdef : zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect f F T = P - S := by
    rfl
  have hmain : P - S = H + H := by
    calc
      P - S = (A + H) - S := by
        exact congrArg (fun x : ℂ => x - S) hP_AH
      _ = (A + H) - (A - H) := by
        exact congrArg (fun x : ℂ => (A + H) - x) hS_AH
      _ = H + H :=
        zetaCompletedExplicitFormulaCorrectionZeroPole_orientationDefect_horizontal_algebra
          A H
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
        f F (h.height_schedule.height u) =
        P - S := hdef
    _ = H + H := hmain
    _ =
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
      rfl

/-- The scheduled project/standard orientation defect tends to zero because it
is two copies of the already controlled scheduled horizontal zero-pole
remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hhorizontal.add hhorizontal
  have hsum_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (zero_add 0)
      hsum
  have heq :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    heq.symm
    hsum_zero

/-- The scheduled rectangles supply boundary regularity for the isolated `s = 1`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (-1 / (w - 1)) *
                zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
            z :=
  zetaCompletedExplicitFormulaCorrectionOnePole_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary regularity for the named isolated
`s = 1` correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_scheduled_regularAt_all_boundary_points
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
        ContinuousAt
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z ∧
          DifferentiableAt ℂ
            (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z :=
  zetaCompletedExplicitFormulaCorrectionOnePoleKernel_regularAt_all_boundary_points_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary continuity for the isolated `s = 1`
correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ =>
        (-1 / (w - 1)) *
          zetaCompletedExplicitFormulaPhi f (w - 1 / 2))
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionOnePole_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- The scheduled rectangles supply boundary continuity for the named isolated
`s = 1` correction kernel at every scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleKernel_scheduled_continuousOn_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ContinuousOn
      (fun w : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      (explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :=
  zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousOn_boundary_of_avoidsBoundary
    f F h.phi_control (h.height_schedule.height u)
    (h.height_schedule.avoids_boundary u)

/-- Scheduled residue inputs for the isolated `s = 1` correction kernel at
eventually positive heights. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_eventually_tangentResidueInputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      (1 : ℂ) ∈ explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
        (∀ z : ℂ,
          z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
            ContinuousAt
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
                z ∧
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
                z) ∧
        Tendsto
          (fun z : ℂ =>
            (z - 1) *
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (𝓝[≠] (1 : ℂ))
          (𝓝 (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionOnePole_tangentResidueInputs_of_pos_height
        f F h.phi_control (h.height_schedule.height u) hu
        (h.height_schedule.avoids_boundary u))

/-- Right-face one-pole Cauchy limit for the `s = 0` correction pole. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  sorry

/-- The scheduled right-face off-pole `s = 1` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- The scheduled Cauchy/oscillatory cancellation package for the right-face
off-pole `s = 1` correction integral.

This is the analytic step obtained by applying the scheduled contour
cancellation or integration-by-parts package to the fixed-displacement
vertical face.  The inverse-quadratic decay is not a pointwise
denominator-separation consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  sorry

/-- Shared scheduled zero-excised strip data for the two horizontal edges, packaged from
an already constructed scheduled carrier and its top/bottom membership proofs. -/
theorem explicitFormulaHorizontalEdges_zeroExcisedStrip_of_mem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) ∧
      (∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) := by
  exact ⟨E, hTopMem, hBottomMem⟩

/-- The split horizontal edge envelope with exponents `(0, 2)` is bounded by a fixed
inverse-quadratic height envelope.

This is the deterministic normalization of the horizontal-edge owner envelope; no
top/bottom geometry is involved in this step. -/
theorem horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c))) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ T : ℝ,
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T
          ≤ B * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0 *
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        2 *
      horizontalEdgeLength F.c
  refine ⟨C + 1, add_pos_of_nonneg_of_pos ?_ zero_lt_one, ?_⟩
  · exact mul_nonneg
      (mul_nonneg
        (le_of_lt
          (h.logderiv_control.zeroExcisedStripBoundConstant_pos
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0))
        (le_of_lt
          (h.phi_control.verticalStripRapidDecayConstant_pos
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2)
            2)))
      (abs_nonneg ((1 - F.c) - F.c))
  · intro T
    let q : ℝ := (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))
    have hq_nonneg : 0 ≤ q := by
      exact le_of_lt (zpow_pos (one_add_norm_pos (F.rectangle T).T) (-(2 : ℤ)))
    have hC_le : C ≤ C + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hscaled : C * q ≤ (C + 1) * q :=
      mul_le_mul_of_nonneg_right hC_le hq_nonneg
    have hrewrite :
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T =
          C * q := by
      have hraw :
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              h.phi_control h.logderiv_control F E 0 2 T =
            C *
              ((1 + ‖T‖) ^ (0 : ℕ) *
                (1 + ‖T‖) ^ (-(2 : ℤ))) := by
        exact horizontalEnvelopeSplit_reassociate
          (h.logderiv_control.zeroExcisedStripBoundConstant
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0)
          (h.phi_control.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2)
            2)
          (horizontalEdgeLength F.c)
          ((1 + ‖T‖) ^ (0 : ℕ))
          ((1 + ‖T‖) ^ (-(2 : ℤ)))
      have hpow_zero :
          (1 + ‖T‖) ^ (0 : ℕ) = (1 : ℝ) :=
        pow_zero (1 + ‖T‖)
      have hdecay_transport :
          (1 + ‖T‖) ^ (-(2 : ℤ)) = q := by
        rfl
      have hcollapse :
          (1 + ‖T‖) ^ (0 : ℕ) *
              (1 + ‖T‖) ^ (-(2 : ℤ)) =
            q := by
        calc
          (1 + ‖T‖) ^ (0 : ℕ) *
              (1 + ‖T‖) ^ (-(2 : ℤ)) =
              (1 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
            exact congrArg
              (fun x : ℝ => x * (1 + ‖T‖) ^ (-(2 : ℤ)))
              hpow_zero
          _ = (1 + ‖T‖) ^ (-(2 : ℤ)) := by
            exact one_mul ((1 + ‖T‖) ^ (-(2 : ℤ)))
          _ = q := by
            exact hdecay_transport
      exact Eq.trans hraw (congrArg (fun x : ℝ => C * x) hcollapse)
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ (C + 1) * q)
      hrewrite.symm
      hscaled

/-- Top horizontal-edge data sufficient to convert the existing split-envelope
estimate into the inverse-quadratic bound consumed by the vertical channel. -/
theorem explicitFormulaTopLineIntegral_inverseQuadraticEnvelope_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ Btop : ℝ,
      0 < Btop ∧
      ∀ T : ℝ,
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T
          ≤ Btop * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
  match horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_ownerGap
      f F h E with
  | ⟨B, hBpos, hB⟩ =>
      exact ⟨B, hBpos, hB⟩

/-- Bottom horizontal-edge data sufficient to convert the existing split-envelope
estimate into the inverse-quadratic bound consumed by the vertical channel. -/
theorem explicitFormulaBottomLineIntegral_inverseQuadraticEnvelope_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ Bbottom : ℝ,
      0 < Bbottom ∧
      ∀ T : ℝ,
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T
          ≤ Bbottom * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
  match horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_ownerGap
      f F h E with
  | ⟨B, hBpos, hB⟩ =>
      exact ⟨B, hBpos, hB⟩

/-- Scheduled top horizontal-edge inverse-quadratic estimate.

This is the top-edge half of the horizontal-control package.  It is separated
from the top-minus-bottom statement so the final owner theorem is only norm
subadditivity and scalar algebra. -/
theorem explicitFormulaTopLineIntegral_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ Btop : ℝ,
      0 < Btop ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaTopLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Btop *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match explicitFormulaTopLineIntegral_inverseQuadraticEnvelope_ownerGap f F h E hTopMem with
  | ⟨Btop, hBtop_pos, hBtop⟩ =>
      refine ⟨Btop, hBtop_pos, ?_⟩
      intro u
      have hedge :
          ‖zetaCompletedExplicitFormulaTopLineIntegral
              f (F.rectangle (h.height_schedule.height u))‖
            ≤ horizontalUnorderedFamilyEdgeEnvelopeSplit
                h.phi_control h.logderiv_control F E 0 2
                (h.height_schedule.height u) :=
        zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelopeSplit
          h.phi_control h.logderiv_control
          (F.rectangle (h.height_schedule.height u)) E
          (fun x hx => hTopMem u x hx) 0 2
      exact le_trans hedge (hBtop (h.height_schedule.height u))

/-- Scheduled bottom horizontal-edge inverse-quadratic estimate. -/
theorem explicitFormulaBottomLineIntegral_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ Bbottom : ℝ,
      0 < Bbottom ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaBottomLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Bbottom *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match explicitFormulaBottomLineIntegral_inverseQuadraticEnvelope_ownerGap f F h E hBottomMem with
  | ⟨Bbottom, hBbottom_pos, hBbottom⟩ =>
      refine ⟨Bbottom, hBbottom_pos, ?_⟩
      intro u
      have hedge :
          ‖zetaCompletedExplicitFormulaBottomLineIntegral
              f (F.rectangle (h.height_schedule.height u))‖
            ≤ horizontalUnorderedFamilyEdgeEnvelopeSplit
                h.phi_control h.logderiv_control F E 0 2
                (h.height_schedule.height u) :=
        zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelopeSplit
          h.phi_control h.logderiv_control
          (F.rectangle (h.height_schedule.height u)) E
          (fun x hx => hBottomMem u x hx) 0 2
      exact le_trans hedge (hBbottom (h.height_schedule.height u))

/-- Norm-subadditivity and scalar accounting for the top-minus-bottom
horizontal estimate. -/
theorem explicitFormulaHorizontalSideDifference_inverseQuadraticBound_from_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (Btop Bbottom : ℝ)
    (hBtop :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaTopLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Btop *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hBbottom :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaBottomLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Bbottom *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaTopLineIntegral
            f (F.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaBottomLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
        ≤ (Btop + Bbottom) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let T : ℝ := h.height_schedule.height u
  let q : ℝ := (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))
  have hnorm :
      ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
        ≤
          ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ +
            ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ :=
    norm_sub_le
      (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
  have hedges :
      ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ +
          ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
        ≤ Btop * q + Bbottom * q :=
    add_le_add (hBtop u) (hBbottom u)
  have hcombine :
      Btop * q + Bbottom * q = (Btop + Bbottom) * q :=
    (add_mul Btop Bbottom q).symm
  exact le_trans (le_trans hnorm hedges) (le_of_eq hcombine)

/-- Horizontal-edge inverse-quadratic cancellation estimate for the scheduled
top-minus-bottom horizontal side difference.

This is the horizontal estimate consumed by the correction-channel users. -/
theorem explicitFormulaHorizontalSideDifference_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match explicitFormulaTopLineIntegral_inverseQuadraticBound_ownerGap f F h E hTopMem,
    explicitFormulaBottomLineIntegral_inverseQuadraticBound_ownerGap f F h E hBottomMem with
  | ⟨Btop, hBtop_pos, hBtop⟩, ⟨Bbottom, hBbottom_pos, hBbottom⟩ =>
      exact
        ⟨Btop + Bbottom, add_pos hBtop_pos hBbottom_pos,
          explicitFormulaHorizontalSideDifference_inverseQuadraticBound_from_edges
            f F h Btop Bbottom hBtop hBbottom⟩

/-- Inserting the package height schedule into the unscheduled horizontal
inverse-quadratic estimate gives the scheduled estimate. -/
theorem explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_of_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB :
      ∀ T : ℝ,
        ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
          ≤ B * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
        ≤ B *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  exact hB (h.height_schedule.height u)

/-- Shared scheduled horizontal-edge inverse-quadratic cancellation estimate.

Both off-pole correction faces consume the same top-minus-bottom horizontal
side difference, so the face-specific estimates below are wrappers over this
single scheduled transport of the horizontal owner estimate. -/
theorem explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match explicitFormulaHorizontalSideDifference_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨B, hBpos, hB⟩ =>
      exact ⟨B, hBpos, hB⟩

/-- Horizontal-edge cancellation for the scheduled right-face opposite-pole
integral.  This is the decay of the horizontal remainder exposed by the Cauchy
rectangle identity, not a vertical pointwise denominator estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic assembly of the scheduled Cauchy rectangle cancellation and the
horizontal-edge inverse-quadratic bound for the right-face off-pole pole. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_ownerGap
      f F h,
    zetaCompletedExplicitFormulaCorrectionRightOnePole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨A, hApos, hA⟩, ⟨B, hBpos, hB⟩ =>
      refine ⟨A + B, add_pos hApos hBpos, ?_⟩
      intro u
      let q : ℝ :=
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
      have hrectangle :
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u‖
            ≤
              ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
                A * q :=
        hA u
      have hhorizontal :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
            ≤ B * q :=
        hB u
      have hcombined :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ + A * q
            ≤ B * q + A * q :=
        add_le_add_right hhorizontal (A * q)
      have hcommuted :
          B * q + A * q = A * q + B * q :=
        add_comm (B * q) (A * q)
      have hfactored :
          A * q + B * q = (A + B) * q :=
        (add_mul A B q).symm
      have htarget :
          B * q + A * q = (A + B) * q :=
        Eq.trans hcommuted hfactored
      exact le_trans hrectangle (le_trans hcombined (le_of_eq htarget))

/-- The scheduled Cauchy/oscillatory cancellation package for the right-face
off-pole `s = 1` correction integral.

The proof is now localized to the finite Cauchy rectangle cancellation, the
horizontal-edge cancellation estimate, and the final inverse-quadratic algebra. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
      f F h E hTopMem hBottomMem

/-- Definition transport from the named scheduled right-face oscillatory integral
to the explicit integral used in the correction channel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- Scheduled Cauchy cancellation for the explicit right-face off-pole `s = 1`
correction integral.

The right edge has fixed real part, so this estimate is not a consequence of a
pointwise denominator-separation bound on an expanding interval.  Its analytic
content is the contour/oscillatory cancellation that converts the off-pole
vertical integral into an inverse-quadratic scheduled tail.  The following
named-integral theorem only unfolds the owner definition. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖∫ t in
            Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 /
                (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨M, hMpos, hbound⟩ =>
      refine ⟨M, hMpos, ?_⟩
      intro u
      have hnamed :
          (∫ t in
              Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 /
                  (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1)) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
            zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
              f F h u :=
        zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_eq_named
          f F h u
      exact Eq.symm hnamed ▸ hbound u

/-- Definition transport from the right-face off-pole correction integral to its
explicit oscillatory-integral cancellation estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic transport from the scheduled right-face Cauchy cancellation estimate
to the public inverse-quadratic off-pole bound.  The only remaining content of
the preceding theorem is the scheduled contour cancellation itself. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Off-pole right-face correction tail estimate for the `s = 1` pole.

This public estimate is a thin wrapper over the scheduled Cauchy cancellation
theorem.  It deliberately does not assert that pointwise denominator separation
alone controls the expanding vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_offPoleTailBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- The scheduled inverse-quadratic tail weight tends to zero on any cofinal
height schedule. -/
theorem zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  have hheight_norm :
      Tendsto
        (fun u : ℝ => ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_norm_atTop_atTop.comp hSchedule.cofinal
  have hheight_norm_plus_one :
      Tendsto
        (fun u : ℝ => 1 + ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) hheight_norm
  have hexponent_negative : (-(2 : ℤ)) < 0 :=
    Int.negSucc_lt_zero 1
  have hinverse_quadratic :
      Tendsto
        (fun u : ℝ =>
          (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    (tendsto_zpow_atTop_zero hexponent_negative).comp
      hheight_norm_plus_one
  have hscaled :
      Tendsto
        (fun u : ℝ =>
          M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 (M * 0)) :=
    hinverse_quadratic.const_mul M
  have hzero : M * 0 = 0 :=
    mul_zero M
  exact hzero ▸ hscaled

/-- The off-pole right-face correction tail majorant tends to zero along the
cofinal scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tailMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule M

/-- The right-face opposite-pole correction integral vanishes by the off-pole
denominator bound and rapid vertical-strip decay of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (M : ℝ)
    (hMpos : 0 < M)
    (hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    squeeze_zero_norm hbound
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tailMajorant_tendsto_zero
        f F h M)

/-- Right-face one-pole Cauchy limit for the opposite `s = 1` pole contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  match
    ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
      h with
  | ⟨E, hTopMem, hBottomMem⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_offPoleTailBound_ownerGap
          f F h E hTopMem hBottomMem with
      | ⟨C, hCpos, hCbound⟩ =>
          exact
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
              f F h C hCpos hCbound

/-- The scheduled left-face off-pole `s = 0` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- The scheduled horizontal remainder for the `s = 0` single-pole rectangle. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u) -
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)

/-- The scheduled horizontal remainder for the `s = 1` single-pole rectangle. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u) -
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)

/-- The scheduled `s = 0` horizontal single-pole remainder unfolds to its top-minus-bottom
definition. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u =
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u) :=
  rfl

/-- The isolated scheduled `s = 0` horizontal remainder is bounded by the two
single-pole horizontal edges. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ := by
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  change ‖U - B‖ ≤ ‖U‖ + ‖B‖
  exact norm_sub_le U B

/-- A pointwise bound on the top `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- A pointwise bound on the bottom `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- Pointwise top-edge decay for the isolated `s = 0` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaTopPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Pointwise bottom-edge decay for the isolated `s = 0` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaBottomPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Top `s = 0` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Bottom `s = 0` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Isolated scheduled `s = 0` horizontal remainder bound from the two
single-pole horizontal edge estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hinvTop :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (hinvBottom :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  let T : ℝ := h.height_schedule.height u
  let C : ℝ :=
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) N *
    (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))
  have htop :
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T hinvTop N
  have hbottom :
      ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T hinvBottom N
  have hedges :
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
          ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_edges
      f F h u
  have hsum :
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c + C * horizontalEdgeLength F.c :=
    add_le_add htop hbottom
  exact le_trans hedges hsum

/-- The top horizontal `s = 0` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaTopPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- The bottom horizontal `s = 0` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaBottomPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- Scheduled isolated `s = 0` horizontal remainder bound at heights where the
horizontal pole denominators are separated by the height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one
      f hPhi F h u
      (fun x hx =>
        zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height
          F (h.height_schedule.height u) x hT)
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height
          F (h.height_schedule.height u) x hT)
      N

/-- The isolated scheduled `s = 0` horizontal remainder is eventually bounded by
an inverse-quadratic height envelope. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    let C : ℝ :=
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) 2
    let L : ℝ := horizontalEdgeLength F.c
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  change
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  exact
    (h.height_schedule.eventually_height_gt 1).mono
      (fun u hu =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖ := by
          have hle_height : 1 ≤ h.height_schedule.height u :=
            le_of_lt hu
          have hheight_le_norm :
              h.height_schedule.height u ≤ ‖h.height_schedule.height u‖ := by
            calc
              h.height_schedule.height u ≤ |h.height_schedule.height u| := by
                exact le_abs_self (h.height_schedule.height u)
              _ = ‖h.height_schedule.height u‖ := by
                exact (Real.norm_eq_abs (h.height_schedule.height u)).symm
          exact le_trans hle_height hheight_le_norm
        have hraw :
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖
              ≤ C * q * L + C * q * L :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
            f h.phi_control F h u hT 2
        have hedge :
            C * q * L = C * L * q := by
          calc
            C * q * L = (C * q) * L := by
              rfl
            _ = C * (q * L) := by
              exact mul_assoc C q L
            _ = C * (L * q) := by
              exact congrArg (fun x : ℝ => C * x) (mul_comm q L)
            _ = C * L * q := by
              exact (mul_assoc C L q).symm
        have hsum :
            C * q * L + C * q * L = (C * L + C * L) * q := by
          calc
            C * q * L + C * q * L = C * L * q + C * L * q := by
              exact congrArg₂ (fun x y : ℝ => x + y) hedge hedge
            _ = (C * L + C * L) * q := by
              exact (add_mul (C * L) (C * L) q).symm
        Eq.subst
          (motive := fun x : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖ ≤ x)
          hsum
          hraw)

/-- The isolated scheduled `s = 0` horizontal remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u)
      atTop
      (𝓝 0) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
      f F h
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule (C * L + C * L)
  exact squeeze_zero_norm' hbound hmajorant

/-- The scheduled `s = 1` horizontal single-pole remainder unfolds to its top-minus-bottom
definition. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u =
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) :=
  rfl

/-- The isolated scheduled `s = 1` horizontal remainder is bounded by the two
single-pole horizontal edges. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ := by
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  change ‖U - B‖ ≤ ‖U‖ + ‖B‖
  exact norm_sub_le U B

/-- A pointwise bound on the top `s = 1` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- A pointwise bound on the bottom `s = 1` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- The top horizontal `s = 1` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaTopPath_onePoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ := by
      calc
        ‖z.im‖ =
            ‖(zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im‖ := by
          exact congrArg norm
            (Eq.trans
              (Complex.sub_im
                (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) (1 : ℂ))
              (Eq.trans
                (congrArg
                  (fun y : ℝ =>
                    (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im - y)
                  Complex.one_im)
                (sub_zero
                  (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).im)))
        _ = ‖(F.rectangle T).T‖ :=
          zetaCompletedExplicitFormulaTopPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- The bottom horizontal `s = 1` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaBottomPath_onePoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ := by
      calc
        ‖z.im‖ =
            ‖(zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im‖ := by
          exact congrArg norm
            (Eq.trans
              (Complex.sub_im
                (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) (1 : ℂ))
              (Eq.trans
                (congrArg
                  (fun y : ℝ =>
                    (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im - y)
                  Complex.one_im)
                (sub_zero
                  (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).im)))
        _ = ‖(F.rectangle T).T‖ :=
          zetaCompletedExplicitFormulaBottomPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- Pointwise top-edge decay for the isolated `s = 1` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaTopPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Pointwise bottom-edge decay for the isolated `s = 1` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_right (norm_nonneg b) hinv
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaBottomPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Top `s = 1` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Bottom `s = 1` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Isolated scheduled `s = 1` horizontal remainder bound from the two
single-pole horizontal edge estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  let T : ℝ := h.height_schedule.height u
  let C : ℝ :=
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) N *
    (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))
  have htop :
      ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T
      (fun x hx =>
        zetaCompletedExplicitFormulaTopPath_onePoleInv_norm_le_one_of_one_le_height
          F T x hT)
      N
  have hbottom :
      ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomPath_onePoleInv_norm_le_one_of_one_le_height
          F T x hT)
      N
  have hedges :
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖ +
          ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_edges
      f F h u
  have hsum :
      ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c + C * horizontalEdgeLength F.c :=
    add_le_add htop hbottom
  exact le_trans hedges hsum

/-- The isolated scheduled `s = 1` horizontal remainder is eventually bounded by
an inverse-quadratic height envelope. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    let C : ℝ :=
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) 2
    let L : ℝ := horizontalEdgeLength F.c
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  change
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  exact
    (h.height_schedule.eventually_height_gt 1).mono
      (fun u hu =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖ := by
          have hle_height : 1 ≤ h.height_schedule.height u :=
            le_of_lt hu
          have hheight_le_norm :
              h.height_schedule.height u ≤ ‖h.height_schedule.height u‖ := by
            calc
              h.height_schedule.height u ≤ |h.height_schedule.height u| := by
                exact le_abs_self (h.height_schedule.height u)
              _ = ‖h.height_schedule.height u‖ := by
                exact (Real.norm_eq_abs (h.height_schedule.height u)).symm
          exact le_trans hle_height hheight_le_norm
        have hraw :
            ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u‖
              ≤ C * q * L + C * q * L :=
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
            f h.phi_control F h u hT 2
        have hedge :
            C * q * L = C * L * q := by
          calc
            C * q * L = (C * q) * L := by
              rfl
            _ = C * (q * L) := by
              exact mul_assoc C q L
            _ = C * (L * q) := by
              exact congrArg (fun x : ℝ => C * x) (mul_comm q L)
            _ = C * L * q := by
              exact (mul_assoc C L q).symm
        have hsum :
            C * q * L + C * q * L = (C * L + C * L) * q := by
          calc
            C * q * L + C * q * L = C * L * q + C * L * q := by
              exact congrArg₂ (fun x y : ℝ => x + y) hedge hedge
            _ = (C * L + C * L) * q := by
              exact (add_mul (C * L) (C * L) q).symm
        Eq.subst
          (motive := fun x : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u‖ ≤ x)
          hsum
          hraw)

/-- The isolated scheduled `s = 1` horizontal remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u)
      atTop
      (𝓝 0) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
      f F h
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule (C * L + C * L)
  exact squeeze_zero_norm' hbound hmajorant

/-- The scheduled `s = 0` boundary integral is the right side minus the left side plus
the scheduled `s = 0` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  change C = R - L + H
  calc
    C = R - L + U - B := by
      rfl
    _ = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = R - L + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = R - L + (U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (sub_eq_add_neg U B).symm
    _ = R - L + H := by
      rfl

/-- The scheduled genuine `s = 0` contour boundary is the vertical-tangent
difference plus the scheduled horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u
  have htangent :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        R * Complex.I - L * Complex.I + U - B :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hH : H = U - B := by
    rfl
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T := by
      rfl
    _ = R * Complex.I - L * Complex.I + U - B := htangent
    _ = R * Complex.I - L * Complex.I + (U - B) := by
      calc
        R * Complex.I - L * Complex.I + U - B =
            (R * Complex.I - L * Complex.I + U) + -B := by
          exact sub_eq_add_neg (R * Complex.I - L * Complex.I + U) B
        _ = R * Complex.I - L * Complex.I + (U + -B) := by
          exact add_assoc (R * Complex.I - L * Complex.I) U (-B)
        _ = R * Complex.I - L * Complex.I + (U - B) := by
          exact congrArg
            (fun x : ℂ => R * Complex.I - L * Complex.I + x)
            (sub_eq_add_neg U B).symm
    _ = R * Complex.I - L * Complex.I + H := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x) hH.symm

/-- The scheduled `s = 1` boundary integral is the right side minus the left side plus
the scheduled `s = 1` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  change C = R - L + H
  calc
    C = R - L + U - B := by
      rfl
    _ = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = R - L + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = R - L + (U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (sub_eq_add_neg U B).symm
    _ = R - L + H := by
      rfl

/-- The early right-face off-pole `s = 1` vertical integral isolated from the
single-pole rectangle boundary identity. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change R = L - H + C
  exact rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq R L H C hC

/-- The scheduled genuine `s = 1` contour boundary is the vertical-tangent
difference plus the scheduled horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u
  have htangent :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        R * Complex.I - L * Complex.I + U - B :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hH : H = U - B := by
    rfl
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T := by
      rfl
    _ = R * Complex.I - L * Complex.I + U - B := htangent
    _ = R * Complex.I - L * Complex.I + (U - B) := by
      calc
        R * Complex.I - L * Complex.I + U - B =
            (R * Complex.I - L * Complex.I + U) + -B := by
          exact sub_eq_add_neg (R * Complex.I - L * Complex.I + U) B
        _ = R * Complex.I - L * Complex.I + (U + -B) := by
          exact add_assoc (R * Complex.I - L * Complex.I) U (-B)
        _ = R * Complex.I - L * Complex.I + (U - B) := by
          exact congrArg
            (fun x : ℂ => R * Complex.I - L * Complex.I + x)
            (sub_eq_add_neg U B).symm
    _ = R * Complex.I - L * Complex.I + H := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x) hH.symm

/-- Solve the corrected tangent-contour boundary identity for the scheduled
right `s = 1` vertical face.  This is the non-circular replacement for the old
unweighted rectangle-boundary bookkeeping. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hC : C = R * Complex.I - L * Complex.I + H :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F h u
  have hI_mul_I : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  have hnegI_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by
        exact neg_mul Complex.I Complex.I
      _ = -(-(1 : ℂ)) := by
        exact congrArg Neg.neg hI_mul_I
      _ = (1 : ℂ) := by
        exact neg_neg (1 : ℂ)
  have hC_mul_negI :
      C * (-Complex.I) = R - L + H * (-Complex.I) := by
    calc
      C * (-Complex.I) = (R * Complex.I - L * Complex.I + H) * (-Complex.I) := by
        exact congrArg (fun x : ℂ => x * (-Complex.I)) hC
      _ = ((R * Complex.I - L * Complex.I) + H) * (-Complex.I) := by
        rfl
      _ = (R * Complex.I - L * Complex.I) * (-Complex.I) + H * (-Complex.I) := by
        exact add_mul (R * Complex.I - L * Complex.I) H (-Complex.I)
      _ = ((R * Complex.I) + -(L * Complex.I)) * (-Complex.I) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x * (-Complex.I) + H * (-Complex.I))
          (sub_eq_add_neg (R * Complex.I) (L * Complex.I))
      _ =
          ((R * Complex.I) * (-Complex.I) + (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x + H * (-Complex.I))
          (add_mul (R * Complex.I) (-(L * Complex.I)) (-Complex.I))
      _ =
          (R * (Complex.I * (-Complex.I)) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_assoc R Complex.I (-Complex.I))
      _ =
          (R * (-(Complex.I * Complex.I)) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_neg Complex.I Complex.I)
      _ =
          (R * (1 : ℂ) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          hnegI_mul_I
      _ =
          (R +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_one R)
      _ =
          (R +
              -((L * Complex.I) * (-Complex.I))) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + x) + H * (-Complex.I))
          (neg_mul (L * Complex.I) (-Complex.I))
      _ =
          (R +
              -(L * (Complex.I * (-Complex.I)))) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -x) + H * (-Complex.I))
          (mul_assoc L Complex.I (-Complex.I))
      _ =
          (R + -(L * (1 : ℂ))) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -(L * x)) + H * (-Complex.I))
          hnegI_mul_I
      _ = (R + -L) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -x) + H * (-Complex.I))
          (mul_one L)
      _ = R - L + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x + H * (-Complex.I))
          (sub_eq_add_neg R L).symm
  have hsolve :
      R = L + C * (-Complex.I) - H * (-Complex.I) := by
    have hstep :
        C * (-Complex.I) - H * (-Complex.I) = R - L := by
      calc
        C * (-Complex.I) - H * (-Complex.I) =
            (R - L + H * (-Complex.I)) - H * (-Complex.I) := by
          exact congrArg (fun x : ℂ => x - H * (-Complex.I)) hC_mul_negI
        _ = ((R - L) + H * (-Complex.I)) + -(H * (-Complex.I)) := by
          exact sub_eq_add_neg (R - L + H * (-Complex.I)) (H * (-Complex.I))
        _ = (R - L) + (H * (-Complex.I) + -(H * (-Complex.I))) := by
          exact add_assoc (R - L) (H * (-Complex.I)) (-(H * (-Complex.I)))
        _ = (R - L) + 0 := by
          exact congrArg (fun x : ℂ => (R - L) + x) (add_neg_cancel (H * (-Complex.I)))
        _ = R - L := by
          exact add_zero (R - L)
    calc
      R = L + (R - L) := by
        exact (add_sub_cancel'_right L R).symm
      _ = L + (C * (-Complex.I) - H * (-Complex.I)) := by
        exact congrArg (fun x : ℂ => L + x) hstep.symm
      _ = L + C * (-Complex.I) - H * (-Complex.I) := by
        exact (add_sub_assoc L (C * (-Complex.I)) (H * (-Complex.I))).symm
  calc
    R = L + C * (-Complex.I) - H * (-Complex.I) := hsolve
    _ = L - C * Complex.I + H * Complex.I := by
      calc
        L + C * (-Complex.I) - H * (-Complex.I) =
            L + -(C * Complex.I) - H * (-Complex.I) := by
          exact congrArg
            (fun x : ℂ => L + x - H * (-Complex.I))
            (mul_neg C Complex.I)
        _ = L - C * Complex.I - H * (-Complex.I) := by
          exact congrArg
            (fun x : ℂ => x - H * (-Complex.I))
            (sub_eq_add_neg L (C * Complex.I)).symm
        _ = L - C * Complex.I - -(H * Complex.I) := by
          exact congrArg
            (fun x : ℂ => L - C * Complex.I - x)
            (mul_neg H Complex.I)
        _ = L - C * Complex.I + H * Complex.I := by
          exact sub_neg_eq_add (L - C * Complex.I) (H * Complex.I)

/-- Norm form of the corrected tangent-boundary identity for the scheduled right
`s = 1` face.  The analytic residue theorem must bound the tangent defect
`left - tangentBoundary * I`; the horizontal remainder is separate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖ +
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    rfl
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - C * Complex.I + H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I
      f F h u
  have hR : R = (L - C * Complex.I) + H * Complex.I :=
    Eq.trans hR_eq_vertical hvertical
  have hnorm :
      ‖(L - C * Complex.I) + H * Complex.I‖ ≤
        ‖L - C * Complex.I‖ + ‖H * Complex.I‖ :=
    norm_add_le (L - C * Complex.I) (H * Complex.I)
  have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
    Complex.norm_I
  have hH_norm : ‖H * Complex.I‖ = ‖H‖ := by
    calc
      ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
        exact norm_mul H Complex.I
      _ = ‖H‖ * 1 := by
        exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
      _ = ‖H‖ := by
        exact mul_one ‖H‖
  have htarget :
      ‖L - C * Complex.I‖ + ‖H * Complex.I‖ =
        ‖L - C * Complex.I‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L - C * Complex.I‖ + x) hH_norm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ ‖L - C * Complex.I‖ + ‖H‖)
    hR.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        ‖(L - C * Complex.I) + H * Complex.I‖ ≤ x)
      htarget
      hnorm)

/-- Norm form of the finite-rectangle `s = 1` correction identity for the scheduled
right face.  This is the exact Cauchy bookkeeping output: the right off-pole face is
controlled by the opposite one-pole face, the one-pole horizontal remainder, and the
single-pole boundary integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_left_horizontal_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    rfl
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - H + C :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary
      f F h u
  have hR : R = L - H + C :=
    Eq.trans hR_eq_vertical hvertical
  have hnorm_add :
      ‖L - H + C‖ ≤ ‖L - H‖ + ‖C‖ :=
    norm_add_le (L - H) C
  have hnorm_sub :
      ‖L - H‖ ≤ ‖L‖ + ‖H‖ :=
    norm_sub_le L H
  have hsum_left :
      ‖L - H‖ + ‖C‖ ≤ (‖L‖ + ‖H‖) + ‖C‖ :=
    add_le_add_right hnorm_sub ‖C‖
  have hsum :
      ‖L - H + C‖ ≤ (‖L‖ + ‖H‖) + ‖C‖ :=
    le_trans hnorm_add hsum_left
  have htarget_assoc :
      (‖L‖ + ‖H‖) + ‖C‖ = ‖L‖ + ‖H‖ + ‖C‖ := by
    rfl
  have hR_norm :
      ‖R‖ = ‖L - H + C‖ :=
    congrArg norm hR
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ ‖L‖ + ‖H‖ + ‖C‖)
    hR_norm.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖L - H + C‖ ≤ x)
      htarget_assoc
      hsum)

/-- Sharp norm form of the finite-rectangle `s = 1` correction cancellation identity.
The residue cancellation to be proved analytically is exactly the combined defect
`left-face + boundary`; the horizontal term is kept separate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    rfl
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - H + C :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary
      f F h u
  have hR : R = L - H + C :=
    Eq.trans hR_eq_vertical hvertical
  have hrepack : L - H + C = (L + C) + -H := by
    calc
      L - H + C = (L + -H) + C := by
        exact congrArg (fun x : ℂ => x + C) (sub_eq_add_neg L H)
      _ = L + (-H + C) := by
        exact add_assoc L (-H) C
      _ = L + (C + -H) := by
        exact congrArg (fun x : ℂ => L + x) (add_comm (-H) C)
      _ = (L + C) + -H := by
        exact (add_assoc L C (-H)).symm
  have hR_repack : R = (L + C) + -H :=
    Eq.trans hR hrepack
  have hnorm :
      ‖(L + C) + -H‖ ≤ ‖L + C‖ + ‖-H‖ :=
    norm_add_le (L + C) (-H)
  have hneg_norm : ‖-H‖ = ‖H‖ :=
    norm_neg H
  have htarget :
      ‖L + C‖ + ‖-H‖ = ‖L + C‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L + C‖ + x) hneg_norm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L + C‖ + ‖H‖)
    hR_repack.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖(L + C) + -H‖ ≤ x)
      htarget
      hnorm)

/-- Solve the corrected tangent-contour boundary identity for the scheduled
left `s = 0` vertical face.  The finite single-pole Cauchy input for this side
is the tangent-boundary defect `right + boundary * I`; the horizontal remainder
is separate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hC : C = R * Complex.I - L * Complex.I + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F h u
  have hI_mul_I : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  have hC_mul_I :
      C * Complex.I = -R + L + H * Complex.I := by
    calc
      C * Complex.I = (R * Complex.I - L * Complex.I + H) * Complex.I := by
        exact congrArg (fun x : ℂ => x * Complex.I) hC
      _ = ((R * Complex.I - L * Complex.I) + H) * Complex.I := by
        rfl
      _ = (R * Complex.I - L * Complex.I) * Complex.I + H * Complex.I := by
        exact add_mul (R * Complex.I - L * Complex.I) H Complex.I
      _ = ((R * Complex.I) + -(L * Complex.I)) * Complex.I + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => x * Complex.I + H * Complex.I)
          (sub_eq_add_neg (R * Complex.I) (L * Complex.I))
      _ =
          ((R * Complex.I) * Complex.I + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => x + H * Complex.I)
          (add_mul (R * Complex.I) (-(L * Complex.I)) Complex.I)
      _ =
          (R * (Complex.I * Complex.I) + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * Complex.I) + H * Complex.I)
          (mul_assoc R Complex.I Complex.I)
      _ =
          (R * (-(1 : ℂ)) + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * Complex.I) + H * Complex.I)
          hI_mul_I
      _ =
          (R * (-(1 : ℂ)) + -((L * Complex.I) * Complex.I)) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + x) + H * Complex.I)
          (neg_mul (L * Complex.I) Complex.I)
      _ =
          (R * (-(1 : ℂ)) + -(L * (Complex.I * Complex.I))) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + -x) + H * Complex.I)
          (mul_assoc L Complex.I Complex.I)
      _ =
          (R * (-(1 : ℂ)) + -(L * (-(1 : ℂ)))) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + -(L * x)) + H * Complex.I)
          hI_mul_I
      _ = (-R + -(L * (-(1 : ℂ)))) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (x + -(L * (-(1 : ℂ)))) + H * Complex.I)
          (mul_neg_one R)
      _ = (-R + -(-L)) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (-R + -x) + H * Complex.I)
          (mul_neg_one L)
      _ = (-R + L) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (-R + x) + H * Complex.I)
          (neg_neg L)
      _ = -R + L + H * Complex.I := by
        rfl
  have hsolve :
      L = R + C * Complex.I - H * Complex.I := by
    have hstep :
        C * Complex.I - H * Complex.I = -R + L := by
      calc
        C * Complex.I - H * Complex.I =
            (-R + L + H * Complex.I) - H * Complex.I := by
          exact congrArg (fun x : ℂ => x - H * Complex.I) hC_mul_I
        _ = ((-R + L) + H * Complex.I) + -(H * Complex.I) := by
          exact sub_eq_add_neg (-R + L + H * Complex.I) (H * Complex.I)
        _ = (-R + L) + (H * Complex.I + -(H * Complex.I)) := by
          exact add_assoc (-R + L) (H * Complex.I) (-(H * Complex.I))
        _ = (-R + L) + 0 := by
          exact congrArg (fun x : ℂ => (-R + L) + x) (add_neg_cancel (H * Complex.I))
        _ = -R + L := by
          exact add_zero (-R + L)
    calc
      L = R + (-R + L) := by
        calc
          L = 0 + L := by
            exact (zero_add L).symm
          _ = (R + -R) + L := by
            exact congrArg (fun x : ℂ => x + L) (add_right_neg R).symm
          _ = R + (-R + L) := by
            exact add_assoc R (-R) L
      _ = R + (C * Complex.I - H * Complex.I) := by
        exact congrArg (fun x : ℂ => R + x) hstep.symm
      _ = R + C * Complex.I - H * Complex.I := by
        exact (add_sub_assoc R (C * Complex.I) (H * Complex.I)).symm
  exact hsolve

/-- Norm form of the corrected tangent-boundary identity for the scheduled left
`s = 0` face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let Ls : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hnamed :
      Ls =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    rfl
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) =
        R + C * Complex.I - H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
      f F h u
  have hLs : Ls = (R + C * Complex.I) + -(H * Complex.I) := by
    calc
      Ls =
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) := hnamed
      _ = R + C * Complex.I - H * Complex.I := hvertical
      _ = (R + C * Complex.I) + -(H * Complex.I) := by
        exact sub_eq_add_neg (R + C * Complex.I) (H * Complex.I)
  have hnorm :
      ‖(R + C * Complex.I) + -(H * Complex.I)‖ ≤
        ‖R + C * Complex.I‖ + ‖-(H * Complex.I)‖ :=
    norm_add_le (R + C * Complex.I) (-(H * Complex.I))
  have hneg_norm : ‖-(H * Complex.I)‖ = ‖H * Complex.I‖ :=
    norm_neg (H * Complex.I)
  have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
    Complex.norm_I
  have hH_mul_I_norm : ‖H * Complex.I‖ = ‖H‖ := by
    calc
      ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
        exact norm_mul H Complex.I
      _ = ‖H‖ * 1 := by
        exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
      _ = ‖H‖ := by
        exact mul_one ‖H‖
  have htail_norm : ‖-(H * Complex.I)‖ = ‖H‖ :=
    Eq.trans hneg_norm hH_mul_I_norm
  have htarget :
      ‖R + C * Complex.I‖ + ‖-(H * Complex.I)‖ =
        ‖R + C * Complex.I‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖R + C * Complex.I‖ + x) htail_norm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ ‖R + C * Complex.I‖ + ‖H‖)
    hLs.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        ‖(R + C * Complex.I) + -(H * Complex.I)‖ ≤ x)
      htarget
      hnorm)

/-- The scheduled tangent-boundary defect is the named left face plus the isolated
zero-pole horizontal remainder with the vertical tangent restored. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hleft :
      L =
        R + C * Complex.I - H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
      f F h u
  change R + C * Complex.I = L + H * Complex.I
  calc
    R + C * Complex.I = (R + C * Complex.I - H * Complex.I) + H * Complex.I := by
      calc
        R + C * Complex.I =
            (R + C * Complex.I) + 0 := by
          exact (add_zero (R + C * Complex.I)).symm
        _ =
            (R + C * Complex.I) + (-(H * Complex.I) + H * Complex.I) := by
          exact congrArg
            (fun x : ℂ => (R + C * Complex.I) + x)
            (neg_add_cancel (H * Complex.I)).symm
        _ =
            ((R + C * Complex.I) + -(H * Complex.I)) + H * Complex.I := by
          exact (add_assoc (R + C * Complex.I) (-(H * Complex.I)) (H * Complex.I)).symm
        _ =
            (R + C * Complex.I - H * Complex.I) + H * Complex.I := by
          exact congrArg
            (fun x : ℂ => x + H * Complex.I)
            (sub_eq_add_neg (R + C * Complex.I) (H * Complex.I)).symm
    _ = L + H * Complex.I := by
      exact congrArg (fun x : ℂ => x + H * Complex.I) hleft.symm

/-- The left scheduled zero-pole face converges to zero once the genuine tangent
Cauchy defect converges to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hdefect :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    hhorizontal.mul tendsto_const_nhds
  have hI_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      hI
  have hsub :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (0 - 0)) :=
    hdefect.sub hI_zero
  have hsub_zero :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u * Complex.I)
          atTop
          (𝓝 z))
      (sub_zero (0 : ℂ))
      hsub
  have hpointwise :
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u) := by
    funext u
    let D : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u * Complex.I
    have hD : D = L + H :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
        f F h u
    change D - H = L
    calc
      D - H = (L + H) - H := by
        exact congrArg (fun x : ℂ => x - H) hD
      _ = (L + H) + -H := by
        exact sub_eq_add_neg (L + H) H
      _ = L + (H + -H) := by
        exact add_assoc L H (-H)
      _ = L + 0 := by
        exact congrArg (fun x : ℂ => L + x) (add_neg_cancel H)
      _ = L := by
        exact add_zero L
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise
    hsub_zero

/-- The genuine zero-pole tangent defect is bounded by the named left face and
the isolated horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_norm_le_left_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let D : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hD : D = L + H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
      f F h u
  have hnorm :
      ‖L + H * Complex.I‖ ≤ ‖L‖ + ‖H * Complex.I‖ :=
    norm_add_le L (H * Complex.I)
  have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
    Complex.norm_I
  have hH_norm : ‖H * Complex.I‖ = ‖H‖ := by
    calc
      ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
        exact norm_mul H Complex.I
      _ = ‖H‖ * 1 := by
        exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
      _ = ‖H‖ := by
        exact mul_one ‖H‖
  have htarget :
      ‖L‖ + ‖H * Complex.I‖ = ‖L‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L‖ + x) hH_norm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L‖ + ‖H‖)
    hD.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖L + H * Complex.I‖ ≤ x)
      htarget
      hnorm)

/-- Quantitative transport from a left-face inverse-quadratic estimate to the
genuine zero-pole tangent-defect inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_inverseQuadratic_of_left_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ C *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hD : D ≤ L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_norm_le_left_add_horizontal
      f F h u
  have hL : L ≤ A * q :=
    hleft u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : L + H ≤ A * q + B * q :=
    add_le_add hL hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  exact le_trans hD (le_trans hsum (le_of_eq hfactor))

/-- The genuine zero-pole tangent defect tends to zero once the named left face
tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    hhorizontal.mul tendsto_const_nhds
  have hI_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      hI
  have hadd :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (0 + 0)) :=
    hleft.add hI_zero
  have hadd_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
              f F h u +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_add 0)
      hadd
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hadd_zero

/-- The genuine zero-pole tangent defect has the same scheduled zero limit as
the named left face, since the isolated horizontal remainder vanishes. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_iff_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) ↔
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) :=
  Iff.intro
    (fun hdefect =>
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
        f F h hdefect)
    (fun hleft =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_leftZeroPole
        f F h hleft)

/-- Residue-value transport for the genuine zero-pole tangent defect.

If the finite tangent rectangle has a constant residue value whose tangent
contribution cancels the right zero-pole limit, then the tangent Cauchy defect
tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_tangentBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hboundary :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  let A : ℂ := (1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hboundary_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I) =
        (fun _u : ℝ => B * Complex.I) := by
    funext u
    have hC :
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B :=
      hboundary u
    exact congrArg (fun z : ℂ => z * Complex.I) hC
  have hboundary_tendsto :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) := by
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B * Complex.I)))
      hboundary_fun.symm
      tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (A + B * Complex.I)) :=
    hright.add hboundary_tendsto
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 z))
    hcancel
    hsum

/-- Residue-value transport from the genuine tangent rectangle to the scheduled
left zero-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hboundary :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_tangentBoundaryResidue
        f F h B hcancel hboundary)

/-- Corrected residue-value transport using the standard rectangle-Cauchy
boundary convention and the explicit project-orientation defect. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hstandard :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B)
    (horientation :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  let A : ℂ := (1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hstandardI_event :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I) =
       ᶠ[atTop]
        (fun _u : ℝ => B * Complex.I) := by
    exact hstandard.mono
      (fun u hu =>
        congrArg (fun z : ℂ => z * Complex.I) hu)
  have hstandardI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    hstandardI_event.tendsto_iff.2 tendsto_const_nhds
  have horientationI_raw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    horientation.mul tendsto_const_nhds
  have horientationI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      horientationI_raw
  have hboundaryI_sum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I + 0)) :=
    hstandardI.add horientationI
  have hboundaryI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      (add_zero (B * Complex.I))
      hboundaryI_sum
  have hprojectI_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u)) * Complex.I) := by
    funext u
    exact congrArg (fun z : ℂ => z * Complex.I)
      (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
        f F h u)
  have hprojectI_split :
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u)) * Complex.I) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u) * Complex.I) := by
    funext u
    exact add_mul
      (zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u))
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
        f F (h.height_schedule.height u))
      Complex.I
  have hprojectI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B * Complex.I)))
      hprojectI_fun.symm
      (Eq.subst
        (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B * Complex.I)))
        hprojectI_split.symm
        hboundaryI)
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (A + B * Complex.I)) :=
    hright.add hprojectI
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 z))
    hcancel
    hsum

/-- Corrected standard-contour residue transport from the finite rectangle
Cauchy convention to the scheduled left zero-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hstandard :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B)
    (horientation :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
        f F h B hcancel hstandard horientation)

/-- Eventual constant-value transport for the corrected standard rectangle
Cauchy boundary convention at positive scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_positiveHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T = B) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) = B := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- Positive-height raw standard-contour Cauchy transport for the isolated
zero-pole local residue.  The raw contour value carries the usual `2πi` factor;
the cancellation identity must therefore be stated for that raw value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_positiveHeight_rawStandardLocalResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I = 0)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect
      f F h
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))))
      hcancel
      (zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryResidueValue_of_positiveHeight
        f F h
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))))
        hpositive)
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero
        f F h)

/-- A positive-height raw standard Cauchy theorem gives the normalized standard
boundary value equal to the local residue. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_normalizedStandardBoundaryResidueValue_of_positiveHeight_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
        f F (h.height_schedule.height u)
        (hpositive (h.height_schedule.height u) hu))

/-- A positive-height raw standard Cauchy theorem gives the normalized `s = 1`
standard boundary value equal to its local residue. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_eventually_normalizedStandardBoundaryResidueValue_of_positiveHeight_rawCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        -zetaCompletedExplicitFormulaPhi f (1 / 2) := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionOnePoleNormalizedStandardRectangleBoundaryIntegral_eq_residue_of_rawCauchy
        f F (h.height_schedule.height u)
        (hpositive (h.height_schedule.height u) hu))

/-- Constant-valued finite tangent residue transport for the genuine zero-pole
tangent defect.  The residue theorem only has to provide a constant boundary
value whose tangent contribution cancels the right-face limit. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_eventually_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hboundary :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  let A : ℂ := (1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hboundary_event :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I) =
       ᶠ[atTop]
        (fun _u : ℝ => B * Complex.I) := by
    exact hboundary.mono
      (fun u hC =>
        congrArg (fun z : ℂ => z * Complex.I) hC)
  have hboundary_tendsto :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    hboundary_event.tendsto_iff.2 tendsto_const_nhds
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (A + B * Complex.I)) :=
    hright.add hboundary_tendsto
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 z))
    hcancel
    hsum

/-- Constant-valued finite tangent residue transport to the scheduled left
zero-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_eventually_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hboundary :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
      f F h
      (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_eventually_tangentBoundaryResidueValue
        f F h B hcancel hboundary)

/-- A positive-height finite tangent residue theorem with value `B` supplies
that scheduled zero-pole tangent residue value eventually. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentBoundaryResidueValue_of_positiveHeight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F T = B) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) = B := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      hpositive (h.height_schedule.height u) hu)

/-- Positive-height finite residue transport from the genuine tangent rectangle
to the scheduled left zero-pole face, with the residue value and cancellation
identity kept explicit. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_positiveHeight_tangentBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ)
    (hcancel :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) +
        B * Complex.I = 0)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F T = B) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_eventually_tangentBoundaryResidueValue
      f F h B hcancel
      (zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_tangentBoundaryResidueValue_of_positiveHeight
        f F h B hpositive)

/-- The late left-face off-pole `s = 0` vertical integral isolated from the
single-pole rectangle boundary identity. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_horizontal_sub_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u -
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change L = R + H - C
  exact leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq R L H C hC

/-- The late left-face off-pole `s = 0` vertical integral is bounded by the
right-boundary defect and the `s = 0` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hL : L = R + H - C :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_horizontal_sub_boundary
      f F h u
  have hrepack : R + H - C = (R - C) + H := by
    calc
      R + H - C = (R + H) + -C := by
        exact sub_eq_add_neg (R + H) C
      _ = R + H + -C := by
        rfl
      _ = R + (H + -C) := by
        exact add_assoc R H (-C)
      _ = R + (-C + H) := by
        exact congrArg (fun x : ℂ => R + x) (add_comm H (-C))
      _ = (R + -C) + H := by
        exact (add_assoc R (-C) H).symm
      _ = (R - C) + H := by
        exact congrArg (fun x : ℂ => x + H) (sub_eq_add_neg R C).symm
  have hL_repack : L = (R - C) + H :=
    Eq.trans hL hrepack
  have hnorm :
      ‖(R - C) + H‖ ≤ ‖R - C‖ + ‖H‖ :=
    norm_add_le (R - C) H
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖R - C‖ + ‖H‖)
    hL_repack.symm
    hnorm

/-- Finite zero-pole Cauchy bookkeeping: the boundary defect of the right
zero-pole face is exactly the left face minus the isolated zero-pole horizontal
remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change R - C = L - H
  calc
    R - C = R + -C := by
      exact sub_eq_add_neg R C
    _ = R + -(R - L + H) := by
      exact congrArg (fun x : ℂ => R + -x) hC
    _ = R + -((R - L) + H) := by
      rfl
    _ = R + (-(R - L) + -H) := by
      exact congrArg (fun x : ℂ => R + x) (neg_add (R - L) H)
    _ = R + (-(R + -L) + -H) := by
      exact congrArg
        (fun x : ℂ => R + (-x + -H))
        (sub_eq_add_neg R L)
    _ = R + ((-(R + -L)) + -H) := by
      rfl
    _ = R + ((-R + -(-L)) + -H) := by
      exact congrArg
        (fun x : ℂ => R + (x + -H))
        (neg_add R (-L))
    _ = R + ((-R + L) + -H) := by
      exact congrArg
        (fun x : ℂ => R + ((-R + x) + -H))
        (neg_neg L)
    _ = (R + (-R + L)) + -H := by
      exact (add_assoc R (-R + L) (-H)).symm
    _ = ((R + -R) + L) + -H := by
      exact congrArg (fun x : ℂ => x + -H) (add_assoc R (-R) L)
    _ = (0 + L) + -H := by
      exact congrArg (fun x : ℂ => (x + L) + -H) (add_right_neg R)
    _ = L + -H := by
      exact congrArg (fun x : ℂ => x + -H) (zero_add L)
    _ = L - H := by
      exact (sub_eq_add_neg L H).symm

/-- Norm bound for the finite zero-pole boundary defect exposed by the
single-pole rectangle identity. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_norm_le_left_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hdefect : R - C = L - H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
      f F h u
  have hnorm : ‖L - H‖ ≤ ‖L‖ + ‖H‖ :=
    norm_sub_le L H
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L‖ + ‖H‖)
    hdefect.symm
    hnorm

/-- Quantitative bookkeeping for the finite zero-pole boundary defect.

Once the true single-pole Cauchy estimate gives an inverse-quadratic bound for
the left off-pole face, this lemma combines it with the isolated horizontal
estimate and produces the exact right-boundary defect bound needed by the
scheduled rectangle cancellation theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_inverseQuadratic_of_left_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ C *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hdefect : D ≤ L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_norm_le_left_add_horizontal
      f F h u
  have hL : L ≤ A * q :=
    hleft u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : L + H ≤ A * q + B * q :=
    add_le_add hL hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  exact le_trans hdefect (le_trans hsum (le_of_eq hfactor))

/-- The finite zero-pole boundary defect tends to zero once the left off-pole
face tends to zero.  The only additional input is the isolated horizontal
remainder, already proved above. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_of_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 - 0)) :=
    hleft.sub hhorizontal
  have hsub_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (sub_zero (0 : ℂ))
      hsub
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hsub_zero

/-- The finite zero-pole boundary defect and the left off-pole face have the
same scheduled limit behavior, since their difference is the isolated horizontal
remainder and that remainder vanishes. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_iff_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
      atTop
      (𝓝 0) ↔
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  constructor
  · intro hboundary
    have hhorizontal :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 0) :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
        f F h
    have hadd :
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 (0 + 0)) :=
      hboundary.add hhorizontal
    have hadd_zero :
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
          atTop
          (𝓝 0) :=
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                  f F (h.height_schedule.height u) -
                zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                  f F (h.height_schedule.height u)) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
            atTop
            (𝓝 z))
        (zero_add 0)
        hadd
    have hpointwise :
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) =
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
      funext u
      let R : ℂ :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)
      let L : ℂ :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)
      let H : ℂ :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u
      let C : ℂ :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)
      have hdefect : R - C = L - H :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_eq_left_sub_horizontal
          f F h u
      change (R - C) + H = L
      calc
        (R - C) + H = (L - H) + H := by
          exact congrArg (fun x : ℂ => x + H) hdefect
        _ = (L + -H) + H := by
          exact congrArg (fun x : ℂ => x + H) (sub_eq_add_neg L H)
        _ = L + (-H + H) := by
          exact add_assoc L (-H) H
        _ = L + 0 := by
          exact congrArg (fun x : ℂ => L + x) (neg_add_cancel H)
        _ = L := by
          exact add_zero L
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpointwise
      hadd_zero
  · intro hleft
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_tendsto_zero_of_leftZeroPole
        f F h hleft

/-- The named scheduled left-face `s = 0` oscillatory integral satisfies the same
boundary-defect plus horizontal-remainder bound as the corresponding vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  have hnamed :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u :=
    rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
    hnamed
    (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u)

/-- The left-zero scheduled cancellation follows from the true remaining
single-pole residue defect, because the isolated `s = 0` horizontal remainder
has already been proved to vanish. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_zeroPoleBoundaryDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hboundary_norm :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖)
        atTop
        (𝓝 0) :=
    tendsto_norm_zero.comp hboundary
  have hhorizontal_norm :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    tendsto_norm_zero.comp hhorizontal
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 (0 + 0)) :=
    hboundary_norm.add hhorizontal_norm
  have hmajorant_zero :
      Tendsto
        (fun u : ℝ =>
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u‖)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun u : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u)‖ +
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u‖)
          atTop
          (𝓝 x))
      (zero_add 0)
      hmajorant
  exact
    squeeze_zero_norm'
      (Eventually.of_forall
        (fun u =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
            f F h u))
      hmajorant_zero

/-- Algebraic assembly of the two true left-zero analytic estimates.

The inputs are exactly the two upstream estimates exposed by the Cauchy
rectangle identity: the residue/boundary defect and the isolated `s = 0`
horizontal remainder.  This lemma contains no analytic shortcut; it only
transports those two bounds through the already proved boundary decomposition. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hboundary :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  have hdecomp :
      ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖ ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    hboundary u
  have hH : H ≤ S + B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + (S + B * q) :=
    add_le_add hD hH
  have hrotate :
      A * q + (S + B * q) = S + (A * q + B * q) := by
    calc
      A * q + (S + B * q) = (A * q + S) + B * q := by
        exact (add_assoc (A * q) S (B * q)).symm
      _ = (S + A * q) + B * q := by
        exact congrArg (fun x : ℝ => x + B * q) (add_comm (A * q) S)
      _ = S + (A * q + B * q) := by
        exact add_assoc S (A * q) (B * q)
  have hfactor :
      A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htarget :
      A * q + (S + B * q) = S + (A + B) * q :=
    Eq.trans hrotate (congrArg (fun x : ℝ => S + x) hfactor)
  exact le_trans hdecomp (le_trans hsum (le_of_eq htarget))

/-- Adding a nonnegative explicit horizontal side term preserves an isolated
zero-pole horizontal inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u‖
        ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hH : H ≤ B * q :=
    hhorizontal u
  have hnonneg : 0 ≤ S :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : B * q ≤ S + B * q := by
    calc
      B * q = 0 + B * q := by
        exact (zero_add (B * q)).symm
      _ ≤ S + B * q := by
        exact add_le_add_right hnonneg (B * q)
  exact le_trans hH hadd

/-- Exact sink for the left-zero scheduled rectangle cancellation from the
genuine tangent-contour Cauchy defect. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (htangent :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let E : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u‖
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hdecomp : L ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    htangent u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + B * q :=
    add_le_add hD hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htail : L ≤ (A + B) * q :=
    le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
  have hEnonneg : 0 ≤ E :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : (A + B) * q ≤ E + (A + B) * q := by
    calc
      (A + B) * q = 0 + (A + B) * q := by
        exact (zero_add ((A + B) * q)).symm
      _ ≤ E + (A + B) * q := by
        exact add_le_add_right hEnonneg ((A + B) * q)
  exact le_trans htail hadd

/-- Exact sink for the left-zero scheduled rectangle cancellation.

The remaining analytic input is the all-height Cauchy estimate for the left
off-pole `s = 0` face.  Once that owner theorem is available, the already
proved boundary-defect identity and isolated horizontal estimate discharge the
scheduled rectangle cancellation statement. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_leftCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_inverseQuadratic_of_left_horizontal
      f F h A B hApos hBpos hleft hhorizontal with
  | ⟨D, hDpos, hD⟩ =>
      exact
        zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
          f F h D B hDpos hBpos hD
          (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
            f F h B hhorizontal)

/-- The scheduled Cauchy rectangle cancellation package for the left-face
off-pole `s = 0` correction integral.

The remaining analytic input is the raw positive-height standard rectangle
Cauchy theorem for the isolated zero-pole kernel, with the honest `2πi`
normalization:
`zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
  f F T =
  (2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))`.
The project/standard orientation defect and normalized-residue transports are
already proved above. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              A *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  sorry

/-- Horizontal-edge cancellation for the scheduled left-face opposite-pole
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic assembly of the scheduled Cauchy rectangle cancellation and the
horizontal-edge inverse-quadratic bound for the left-face off-pole pole. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_ownerGap
      f F h,
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_horizontalEdgeCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨A, hApos, hA⟩, ⟨B, hBpos, hB⟩ =>
      refine ⟨A + B, add_pos hApos hBpos, ?_⟩
      intro u
      let q : ℝ :=
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
      have hrectangle :
          ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u‖
            ≤
              ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
                A * q :=
        hA u
      have hhorizontal :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
            ≤ B * q :=
        hB u
      have hcombined :
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ + A * q
            ≤ B * q + A * q :=
        add_le_add_right hhorizontal (A * q)
      have hcommuted :
          B * q + A * q = A * q + B * q :=
        add_comm (B * q) (A * q)
      have hfactored :
          A * q + B * q = (A + B) * q :=
        (add_mul A B q).symm
      have htarget :
          B * q + A * q = (A + B) * q :=
        Eq.trans hcommuted hfactored
      exact le_trans hrectangle (le_trans hcombined (le_of_eq htarget))

/-- The scheduled Cauchy/oscillatory cancellation package for the left-face
off-pole `s = 0` correction integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_inverseQuadraticBound_from_cauchyHorizontal_ownerGap
      f F h E hTopMem hBottomMem

/-- Definition transport from the named scheduled left-face oscillatory integral
to the explicit integral used in the correction channel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- Scheduled Cauchy cancellation for the explicit left-face off-pole `s = 0`
correction integral.

As on the right face, fixed horizontal displacement and expanding height mean
that denominator separation gives only a local algebraic input.  The inverse
quadratic scheduled bound belongs to the contour/oscillatory cancellation
argument for the whole vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖∫ t in
            Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 /
                zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledContourCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem with
  | ⟨M, hMpos, hbound⟩ =>
      refine ⟨M, hMpos, ?_⟩
      intro u
      have hnamed :
          (∫ t in
              Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 /
                  zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
              f F h u :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_eq_named
          f F h u
      exact Eq.symm hnamed ▸ hbound u

/-- Definition transport from the left-face off-pole correction integral to its
explicit oscillatory-integral cancellation estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Algebraic transport from the scheduled left-face Cauchy cancellation estimate
to the public inverse-quadratic off-pole bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- Off-pole left-face correction tail estimate for the `s = 0` pole.

This public estimate is a thin wrapper over the scheduled Cauchy cancellation
theorem, not a pointwise-majorization estimate on the full expanding interval. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_offPoleTailBound_ownerGap
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_ownerGap
      f F h E hTopMem hBottomMem

/-- The off-pole left-face correction tail majorant tends to zero along the
cofinal scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tailMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule M

/-- The left-face `s = 0` correction integral vanishes by the off-pole
denominator bound and rapid vertical-strip decay of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (M : ℝ)
    (hMpos : 0 < M)
    (hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    squeeze_zero_norm hbound
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tailMajorant_tendsto_zero
        f F h M)

/-- Left-face one-pole Cauchy limit for the `s = 0` pole contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  match
    ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
      h with
  | ⟨E, hTopMem, hBottomMem⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_offPoleTailBound_ownerGap
          f F h E hTopMem hBottomMem with
      | ⟨C, hCpos, hCbound⟩ =>
          exact
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
              f F h C hCpos hCbound

/-- Algebraic transport from the finite `s = 1` rectangle boundary residue limit
to the left on-pole vertical channel.

The analytic input that remains upstream is the finite single-pole Cauchy
residue limit for `zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral`.
The right off-pole face and the horizontal one-pole remainder are already
controlled in this file. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_rectangleBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) := by
  let K : ℂ := 1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hright.add hhorizontal
  have hboundaryK :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K) :=
    hboundary
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((0 + 0) - K)) :=
    hsum.sub hboundaryK
  have hleft_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u)
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
        f F (h.height_schedule.height u)
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
        f F h u
    let C : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)
    have hC : C = R - L + H :=
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
        f F h u
    change L = R + H - C
    exact leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq R L H C hC
  have htarget :
      (0 + 0 : ℂ) - K = -K := by
    calc
      (0 + 0 : ℂ) - K = 0 - K := by
        exact congrArg (fun z : ℂ => z - K) (zero_add (0 : ℂ))
      _ = 0 + -K := by
        exact sub_eq_add_neg 0 K
      _ = -K := by
        exact zero_add (-K)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (-K)))
    hleft_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Positive-height finite Cauchy equality for the `s = 1` rectangle boundary gives
the scheduled boundary residue limit. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F T =
            1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ =>
        1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  exact hevent.tendsto_iff.2 tendsto_const_nhds

/-- Positive-height finite `s = 1` rectangle Cauchy residue transport to the left
on-pole vertical channel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F T =
            1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_rectangleBoundaryResidue
      f F h
      (zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue
        f F h hpositive)

/-- Algebraic transport from the honest standard `s = 1` contour residue limit
to the left vertical side, with the standard rectangle orientation retained.

This is the value forced by the standard contour convention:
`standard = bottom - top + right * I - left * I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_standardBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (B : ℂ)
    (hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (B * Complex.I)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (B + 0)) :=
    hstandard.add hhorizontal
  have hsumB :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 B) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (add_zero B)
      hsum
  have hsumI :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    hsumB.mul tendsto_const_nhds
  have hleft_expr :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) * Complex.I)
        atTop
        (𝓝 (0 + B * Complex.I)) :=
    hright.add hsumI
  have hleft_expr_target :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u) +
              (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                  f F (h.height_schedule.height u) +
                zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                  f F h u) * Complex.I)
          atTop
          (𝓝 z))
      (zero_add (B * Complex.I))
      hleft_expr
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) * Complex.I) := by
    funext u
    let T : ℝ := h.height_schedule.height u
    let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
    let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
    let H : ℂ := zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u
    let S : ℂ := zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T
    let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
    let D : ℂ := zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
    have hS : S = D - U + R * Complex.I - L * Complex.I := by
      have hRtan :
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
            R * Complex.I :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
          f F T
      have hLtan :
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
            L * Complex.I :=
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
          f F T
      calc
        S =
            D - U +
              zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
          rfl
        _ = D - U + R * Complex.I -
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
          exact congrArg
            (fun z : ℂ =>
              D - U + z -
                zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T)
            hRtan
        _ = D - U + R * Complex.I - L * Complex.I := by
          exact congrArg
            (fun z : ℂ => D - U + R * Complex.I - z)
            hLtan
    have hH : H = U - D := by
      rfl
    have hS_add_H : S + H = R * Complex.I - L * Complex.I := by
      have hDU_cancel : (D - U) + (U - D) = 0 := by
        calc
          (D - U) + (U - D) = (D - U) + -(D - U) := by
            exact congrArg (fun z : ℂ => (D - U) + z) (neg_sub D U).symm
          _ = 0 := by
            exact add_right_neg (D - U)
      calc
        S + H = (D - U + R * Complex.I - L * Complex.I) + H := by
          exact congrArg (fun z : ℂ => z + H) hS
        _ = (D - U + R * Complex.I - L * Complex.I) + (U - D) := by
          exact congrArg (fun z : ℂ => (D - U + R * Complex.I - L * Complex.I) + z) hH
        _ = R * Complex.I - L * Complex.I := by
          calc
            (D - U + R * Complex.I - L * Complex.I) + (U - D) =
                ((D - U) + R * Complex.I - L * Complex.I) + (U - D) := by
              rfl
            _ =
                ((D - U) + (R * Complex.I - L * Complex.I)) + (U - D) := by
              exact congrArg (fun z : ℂ => z + (U - D))
                (add_sub_assoc (D - U) (R * Complex.I) (L * Complex.I))
            _ =
                (R * Complex.I - L * Complex.I) + ((D - U) + (U - D)) := by
              calc
                ((D - U) + (R * Complex.I - L * Complex.I)) + (U - D) =
                    (D - U) + ((R * Complex.I - L * Complex.I) + (U - D)) := by
                  exact add_assoc (D - U) (R * Complex.I - L * Complex.I) (U - D)
                _ =
                    (D - U) + ((U - D) + (R * Complex.I - L * Complex.I)) := by
                  exact congrArg (fun z : ℂ => (D - U) + z)
                    (add_comm (R * Complex.I - L * Complex.I) (U - D))
                _ =
                    ((D - U) + (U - D)) + (R * Complex.I - L * Complex.I) := by
                  exact (add_assoc (D - U) (U - D) (R * Complex.I - L * Complex.I)).symm
                _ =
                    (R * Complex.I - L * Complex.I) + ((D - U) + (U - D)) := by
                  exact add_comm ((D - U) + (U - D)) (R * Complex.I - L * Complex.I)
            _ = (R * Complex.I - L * Complex.I) + 0 := by
              exact congrArg
                (fun z : ℂ => (R * Complex.I - L * Complex.I) + z)
                hDU_cancel
            _ = R * Complex.I - L * Complex.I := by
              exact add_zero (R * Complex.I - L * Complex.I)
    have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
      Complex.I_mul_I
    have hsolve : L = R + (S + H) * Complex.I := by
      calc
        R + (S + H) * Complex.I =
            R + (R * Complex.I - L * Complex.I) * Complex.I := by
          exact congrArg (fun z : ℂ => R + z * Complex.I) hS_add_H
        _ = R + ((R * Complex.I) * Complex.I - (L * Complex.I) * Complex.I) := by
          exact congrArg (fun z : ℂ => R + z)
            (sub_mul (R * Complex.I) (L * Complex.I) Complex.I)
        _ = R + (R * (Complex.I * Complex.I) - L * (Complex.I * Complex.I)) := by
          exact congrArg
            (fun z : ℂ => R + z)
            (congrArg₂ HSub.hSub
              (mul_assoc R Complex.I Complex.I)
              (mul_assoc L Complex.I Complex.I))
        _ = R + (R * (-(1 : ℂ)) - L * (-(1 : ℂ))) := by
          exact congrArg
            (fun z : ℂ => R + (R * z - L * z))
            hI_sq
        _ = R + (-R - -L) := by
          exact congrArg
            (fun z : ℂ => R + z)
            (congrArg₂ HSub.hSub (mul_neg_one R) (mul_neg_one L))
        _ = R + (-R + L) := by
          exact congrArg (fun z : ℂ => R + z) (sub_neg_eq_add (-R) L)
        _ = (R + -R) + L := by
          exact (add_assoc R (-R) L).symm
        _ = 0 + L := by
          exact congrArg (fun z : ℂ => z + L) (add_right_neg R)
        _ = L := by
          exact zero_add L
    exact hsolve.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B * Complex.I)))
    hpointwise.symm
    hleft_expr_target

/-- Positive-height raw standard `s = 1` Cauchy transport to the left vertical
side, with the standard contour normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_positiveHeight_rawStandardCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ =>
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  have hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)))) :=
    hevent.tendsto_iff.2 tendsto_const_nhds
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_standardBoundaryResidue
      f F h
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)))
      hstandard

/-- Positive-height raw standard finite Cauchy theorem for the isolated `s = 1`
correction kernel.

This is the finite contour-residue owner theorem needed by the scheduled
left-face one-pole transport.  It keeps the honest standard-contour
normalization:
`standard boundary = 2πi * residue`, with residue
`-Phi f (1 / 2)` for the kernel `-1 / (z - 1) * Phi f (z - 1 / 2)`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  sorry

/-- Left-face one-pole Cauchy limit for the `s = 1` correction pole, including the
left boundary orientation.

With the honest standard-contour normalization, the upstream finite Cauchy
input is the raw standard boundary theorem for
`zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral`.
The old centered `Phi f 0` target belongs to the later correction-channel
normalization and must not be supplied by this single-pole contour theorem.
-/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_positiveHeight_rawStandardCauchy
      f F h
      (fun T hT =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F h T hT)

/-- The right pole face transports to the pole at `s = 0`, evaluated at the centered
basepoint of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) + 0)) :=
    Tendsto.add hzero hone
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_eq_zero_add_one
      f h.phi_control F (h.height_schedule.height u)
  have htarget :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) + 0 =
        (1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0 :=
    add_zero ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The left pole face transports with the standard-contour one-pole residue
normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝
          (0 + (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    Tendsto.add hzero hone
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_eq_zero_add_one
      f h.phi_control F (h.height_schedule.height u)
  have htarget :
      0 + (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I :=
    zero_add (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Coefficient accounting for the oriented right-minus-left pole faces. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleCoefficient_sub_neg_eq_centeredPoleCoefficient
    (z : ℂ) :
    (1 / (1 / 2 : ℂ)) * z -
        (-(1 / (1 - (1 / 2 : ℂ)) * z)) =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) * z := by
  let a : ℂ := 1 / (1 / 2 : ℂ)
  let b : ℂ := 1 / (1 - (1 / 2 : ℂ))
  change a * z - (-(b * z)) = (a + b) * z
  calc
    a * z - (-(b * z)) = a * z + b * z := by
      exact sub_neg_eq_add (a * z) (b * z)
    _ = (a + b) * z := by
      exact (add_mul a b z).symm

/-- Core correction-channel transport theorem after the contribution normalization:
the explicit two-pole vertical kernel converges to the centered pole coefficient at
`s = 1 / 2`, evaluated against `Φ_f 0`.

This is the remaining analytic orientation/basepoint theorem for the correction channel. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          (-1 / zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t -
              1 / (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
      atTop
      (𝓝
        (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
      f F h
  have hsub :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    Tendsto.sub hright hleft
  have hpointwise :
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          (-1 / zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t -
              1 / (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact Eq.refl _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))))
    hpointwise.symm
    hsub

/-- Concrete correction-channel analytic transport with the standard-contour
single-pole normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  have hkernel :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 / zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t -
                  1 / (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
        atTop
        (𝓝
          (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 / zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t -
                1 / (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
            ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              (-1 / zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t -
                  1 / (zetaCompletedExplicitFormulaLeftPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaLeftPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) := by
      funext u
      exact
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_poleCorrectionVerticalIntegral
          f F (h.height_schedule.height u)
    have hlimit :
        ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
      (zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f).symm
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
      hpointwise.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ =>
              (∫ t in Set.Icc
                  (-(F.rectangle (h.height_schedule.height u)).T)
                  (F.rectangle (h.height_schedule.height u)).T,
                (-1 / zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t -
                    1 / (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1)) *
                  zetaCompletedExplicitFormulaPhi f
                    (zetaCompletedExplicitFormulaRightPath
                      (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) -
                ∫ t in Set.Icc
                    (-(F.rectangle (h.height_schedule.height u)).T)
                    (F.rectangle (h.height_schedule.height u)).T,
                  (-1 / zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t -
                      1 / (zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t - 1)) *
                    zetaCompletedExplicitFormulaPhi f
                      (zetaCompletedExplicitFormulaLeftPath
                        (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
            atTop
            (𝓝 z))
        hlimit
        hkernel)

/-- Correction-channel analytic transport: the scheduled pole-face vertical integral
converges to the standard-contour correction boundary value. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaSelectedScheduledVerticalChannel
          f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction)
      atTop
      (𝓝
        (explicitFormulaSelectedVerticalBoundaryChannel
          f ExplicitFormulaScheduledVerticalChannelProjection.correction)) := by
    have hconcrete :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
      zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
        f F h
    have hpointwise :
        (fun u : ℝ =>
          explicitFormulaSelectedScheduledVerticalChannel
            f F h u ExplicitFormulaScheduledVerticalChannelProjection.correction) =
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u)) := by
      funext u
      exact explicitFormulaSelectedScheduledVerticalChannel_correction_eq f F h u
    have htarget :
        explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction =
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
      explicitFormulaSelectedVerticalBoundaryChannel_correction_eq f
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (explicitFormulaSelectedVerticalBoundaryChannel
            f ExplicitFormulaScheduledVerticalChannelProjection.correction)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
              (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget.symm
      hconcrete)

/-- Owner analytic theorem: the prime vertical-channel transport remainder vanishes along
the scheduled contour heights.  This is the channel-specific logarithmic-derivative
transport estimate; the corresponding convergence to the completed prime contribution is
only the algebraic consequence below. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerPrimeLogDerivativeTransport
      f F h

/-- Owner analytic theorem: the archimedean vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the Gamma/completion channel transport
estimate; the contribution limit is a formal consequence. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h ExplicitFormulaScheduledVerticalChannelProjection.archimedean
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransportAnalytic
        f F h)
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.archimedean) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_archimedean_eq
        f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Owner analytic theorem: the correction vertical-channel transport remainder vanishes
along the scheduled contour heights.  This is the pole-face transport estimate; the
convergence to the correction contribution is a formal consequence. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hprojection :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction)
        atTop
        (𝓝 0) :=
    explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_tendsto_zero_of_selectedChannel_tendsto_boundary
      f F h ExplicitFormulaScheduledVerticalChannelProjection.correction
      (zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransportAnalytic
        f F h)
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaScheduledVerticalChannelProjectionTransportRemainder
            f F (h.height_schedule.height u)
            ExplicitFormulaScheduledVerticalChannelProjection.correction) := by
    funext u
    exact
      (explicitFormulaScheduledVerticalChannelProjectionTransportRemainder_correction_eq
        f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hprojection

/-- Prime vertical-channel convergence from its scheduled transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Archimedean vertical-channel convergence from its scheduled transport-remainder
estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (htransport :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Correction vertical-channel convergence from its scheduled standard-contour
transport-remainder estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
      (htransport :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
              f F (h.height_schedule.height u))
          atTop
          (𝓝 0)) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
    exact
      explicitFormulaScheduledVerticalChannel_tendsto_boundaryContribution_of_tendsto_transportRemainder
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
          (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_contribution_add_transportRemainder
          f F (h.height_schedule.height u))
      htransport

/-- Owner theorem: the prime vertical channel converges to the completed prime
contribution along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- Owner theorem: the archimedean vertical channel converges to the completed
archimedean contribution along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- Owner theorem: the pole-correction vertical channel converges to the
standard-contour correction boundary value along the scheduled contour heights. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
      (h : ExplicitFormulaFamilyAnalyticPackage f F) :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel f F
            (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_of_transportRemainder
      f F h
      (zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
        f F h)

/-- The prime transport remainder vanishes once the prime channel has been transported
to its completed contribution. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h

/-- The archimedean transport remainder vanishes once the archimedean channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h

/-- The correction transport remainder vanishes once the correction channel has been
transported to its completed contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannelTransportRemainder_tendsto_zero_ownerChannelTransportCore
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
