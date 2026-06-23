import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.Owner
import Mathlib.MeasureTheory.Integral.SetIntegral

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
