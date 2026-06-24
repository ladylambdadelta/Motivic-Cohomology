import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner

/-!
# Scheduled prime vertical-channel pieces

This file owns the named scheduled right and left prime vertical integrals.  The
transport estimate file proves convergence statements about these objects; the
definitions themselves are part of the vertical-channel decomposition API.
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

/-- The right path of a contour family is the affine vertical line
`F.c + i t`. -/
theorem zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
      (F.c : ℂ) + t * Complex.I :=
  rfl

/-- The shifted right path in the prime channel is the affine vertical line
`(F.c - 1/2) + i t`. -/
theorem zetaCompletedExplicitFormulaPrime_shiftedRightPath_eq_affineLine
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
      ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
  calc
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
        ((F.c : ℂ) + t * Complex.I) - (1 / 2 : ℂ) := by
      exact congrArg
        (fun z : ℂ => z - (1 / 2 : ℂ))
        (zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine F T t)
    _ = ((F.c : ℂ) + t * Complex.I) + -(1 / 2 : ℂ) := by
      exact sub_eq_add_neg ((F.c : ℂ) + t * Complex.I) (1 / 2 : ℂ)
    _ = (F.c : ℂ) + (t * Complex.I + -(1 / 2 : ℂ)) := by
      exact add_assoc (F.c : ℂ) (t * Complex.I) (-(1 / 2 : ℂ))
    _ = (F.c : ℂ) + (-(1 / 2 : ℂ) + t * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (F.c : ℂ) + z)
        (add_comm (t * Complex.I) (-(1 / 2 : ℂ)))
    _ = ((F.c : ℂ) + -(1 / 2 : ℂ)) + t * Complex.I := by
      exact (add_assoc (F.c : ℂ) (-(1 / 2 : ℂ)) (t * Complex.I)).symm
    _ = ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + t * Complex.I)
        (sub_eq_add_neg (F.c : ℂ) (1 / 2 : ℂ)).symm

/-- The left path of a contour family is the affine vertical line
`(1 - F.c) + i t`. -/
theorem zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
      ((1 : ℂ) - (F.c : ℂ)) + t * Complex.I :=
  rfl

/-- The shifted left path in the prime channel is the affine vertical line
`(1/2 - F.c) + i t`. -/
theorem zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - (1 / 2 : ℂ) =
      ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
  calc
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - (1 / 2 : ℂ) =
        (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) - (1 / 2 : ℂ) := by
      exact congrArg
        (fun z : ℂ => z - (1 / 2 : ℂ))
        (zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine F T t)
    _ = (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) + -(1 / 2 : ℂ) := by
      exact sub_eq_add_neg (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) (1 / 2 : ℂ)
    _ = ((1 : ℂ) - (F.c : ℂ)) + (t * Complex.I + -(1 / 2 : ℂ)) := by
      exact add_assoc ((1 : ℂ) - (F.c : ℂ)) (t * Complex.I) (-(1 / 2 : ℂ))
    _ = ((1 : ℂ) - (F.c : ℂ)) + (-(1 / 2 : ℂ) + t * Complex.I) := by
      exact congrArg
        (fun z : ℂ => ((1 : ℂ) - (F.c : ℂ)) + z)
        (add_comm (t * Complex.I) (-(1 / 2 : ℂ)))
    _ = (((1 : ℂ) - (F.c : ℂ)) + -(1 / 2 : ℂ)) + t * Complex.I := by
      exact
        (add_assoc ((1 : ℂ) - (F.c : ℂ)) (-(1 / 2 : ℂ))
          (t * Complex.I)).symm
    _ = ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + t * Complex.I)
        (sub_eq_add_neg ((1 : ℂ) - (F.c : ℂ)) (1 / 2 : ℂ)).symm

/-- The scheduled right-face von Mangoldt integral for the prime channel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    L ↗Λ
        (zetaCompletedExplicitFormulaRightPath
          (F.rectangle (h.height_schedule.height u)) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath
          (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- The scheduled left-face prime logarithmic-derivative tail. -/
noncomputable def zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaLeftPath
          (F.rectangle (h.height_schedule.height u)) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath
          (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- The scheduled right von Mangoldt integral in affine-line normal form. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineLineIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral f F h u =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        L ↗Λ ((F.c : ℂ) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  have hfun :
      (fun t : ℝ =>
        L ↗Λ
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        L ↗Λ ((F.c : ℂ) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t =
          (F.c : ℂ) + t * Complex.I :=
      zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine
        F (h.height_schedule.height u) t
    have hshift :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - (1 / 2 : ℂ) =
          ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
      zetaCompletedExplicitFormulaPrime_shiftedRightPath_eq_affineLine
        F (h.height_schedule.height u) t
    calc
      L ↗Λ
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
          L ↗Λ ((F.c : ℂ) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            L ↗Λ z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
          hpath
      _ = L ↗Λ ((F.c : ℂ) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            L ↗Λ ((F.c : ℂ) + t * Complex.I) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
  exact congrArg
    (fun φ : ℝ → ℂ =>
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
    hfun

/-- The scheduled left prime logarithmic-derivative tail in affine-line normal
form. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineLineIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        explicitFormulaPrimeLogDerivative (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  have hfun :
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        explicitFormulaPrimeLogDerivative (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t =
          ((1 : ℂ) - (F.c : ℂ)) + t * Complex.I :=
      zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine
        F (h.height_schedule.height u) t
    have hshift :
        zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t - (1 / 2 : ℂ) =
          ((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
      zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine
        F (h.height_schedule.height u) t
    calc
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
          explicitFormulaPrimeLogDerivative (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaPrimeLogDerivative z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
          hpath
      _ = explicitFormulaPrimeLogDerivative (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaPrimeLogDerivative (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
  exact congrArg
    (fun φ : ℝ → ℂ =>
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
    hfun

/-- The scheduled right von Mangoldt integral as the named affine kernel
integral. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineKernelIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral f F h u =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t :=
  zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral_eq_affineLineIntegral
    f F h u

/-- The right inverse-Gamma completion line integral in scheduled affine
normal form. -/
theorem zetaCompletedExplicitFormulaRightInverseGammaLineIntegral_eq_affineKernelIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t =
          zetaCompletedExplicitFormulaRightAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine
        F (h.height_schedule.height u) t
    have hshift :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - (1 / 2 : ℂ) =
          zetaCompletedExplicitFormulaRightCenteredAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_shiftedRightPath_eq_affineLine
        F (h.height_schedule.height u) t
    calc
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            inverseGammaCompletionLogDeriv z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
          hpath
      _ =
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
      _ = zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
        rfl
  exact congrArg
    (fun φ : ℝ → ℂ =>
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
    hfun

/-- The scheduled completed right line is the affine right prime packet plus
the affine right inverse-Gamma packet, before any additivity split of the
finite integral. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_affinePrime_add_inverseGamma_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaRightLineIntegral
        f (F.rectangle (h.height_schedule.height u)) =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t =
          zetaCompletedExplicitFormulaRightAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine
        F (h.height_schedule.height u) t
    have hshift :
        zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - (1 / 2 : ℂ) =
          zetaCompletedExplicitFormulaRightCenteredAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_shiftedRightPath_eq_affineLine
        F (h.height_schedule.height u) t
    have hcompleted_affine :
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
      calc
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
            completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
          exact congrArg
            (fun z : ℂ =>
              completedZetaNegLogDeriv z *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
            hpath
        _ =
            completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
          exact congrArg
            (fun z : ℂ =>
              completedZetaNegLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F t) *
                zetaCompletedExplicitFormulaPhi f z)
            hshift
    exact Eq.trans hcompleted_affine
      (zetaCompletedExplicitFormula_completedRightAffineKernel_eq_prime_add_inverseGamma
        f F t)
  exact congrArg
    (fun φ : ℝ → ℂ =>
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
    hfun

/-- The scheduled completed right line is the sum of the named right prime
and right inverse-Gamma affine integrals, once the two finite-window summands
are known integrable. -/
theorem zetaCompletedExplicitFormulaRightLineIntegral_eq_affinePrime_integral_add_inverseGamma_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hprime :
      IntegrableOn
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T))
    (hinverseGamma :
      IntegrableOn
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) :
    zetaCompletedExplicitFormulaRightLineIntegral
        f (F.rectangle (h.height_schedule.height u)) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t := by
  have hsum :
      zetaCompletedExplicitFormulaRightLineIntegral
          f (F.rectangle (h.height_schedule.height u)) =
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t :=
    zetaCompletedExplicitFormulaRightLineIntegral_eq_affinePrime_add_inverseGamma_integral
      f F h u
  have hadd :
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) =
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) +
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t :=
    integral_add hprime hinverseGamma
  exact Eq.trans hsum hadd

/-- The scheduled left prime logarithmic-derivative tail as the named affine
kernel integral. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineKernelIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u =
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t :=
  zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineLineIntegral
    f F h u

/-- The named scheduled prime integrals reconstruct the scheduled prime
vertical channel. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_scheduledRightVonMangoldt_sub_scheduledLeft
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaPrimeVerticalChannel
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaPrimeScheduledRightVonMangoldtIntegral f F h u -
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel_eq_rightVonMangoldtIntegral_sub_left
    f F (h.height_schedule.height u)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
