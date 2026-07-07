import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.Owner

/-!
# Scheduled archimedean vertical-channel pieces

This file owns the scheduled inverse-Gamma completion channel and its paired
correction channel.  The archimedean transport estimate consumes these names
and proves limit transport from their component estimates.
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

/-- The scheduled inverse-Gamma completion vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
    f F (h.height_schedule.height u)

/-- The scheduled correction vertical channel paired with the inverse-Gamma
completion channel. -/
noncomputable def zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionVerticalChannel
    f F (h.height_schedule.height u)

/-- The scheduled inverse-Gamma completion channel in affine-line normal form. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineLineIntegrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel f F h u =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        inverseGammaCompletionLogDeriv ((F.c : ℂ) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        inverseGammaCompletionLogDeriv (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
          zetaCompletedExplicitFormulaPhi f
            (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  have hright :
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv ((F.c : ℂ) + t * Complex.I) *
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
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
          inverseGammaCompletionLogDeriv ((F.c : ℂ) + t * Complex.I) *
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
      _ = inverseGammaCompletionLogDeriv ((F.c : ℂ) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            inverseGammaCompletionLogDeriv ((F.c : ℂ) + t * Complex.I) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
  have hleft :
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
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
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t - 1 / 2) =
          inverseGammaCompletionLogDeriv (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            inverseGammaCompletionLogDeriv z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath
                  (F.rectangle (h.height_schedule.height u)) t - 1 / 2))
          hpath
      _ = inverseGammaCompletionLogDeriv (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
            zetaCompletedExplicitFormulaPhi f
              (((1 : ℂ) - (F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            inverseGammaCompletionLogDeriv (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
  exact congrArg₂ HSub.hSub
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
      hright)
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        φ t)
      hleft)

/-- The scheduled inverse-Gamma completion channel as the difference of named
affine-kernel integrals. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineKernelIntegrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel f F h u =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t :=
  zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineLineIntegrals
    f F h u

/-- The finite-height archimedean vertical channel in named affine-kernel
normal form. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_affineKernelIntegrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t := by
  have hright :
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
          zetaCompletedExplicitFormulaRightAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_rightPath_eq_affineLine F T t
    have hshift :
        zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            (1 / 2 : ℂ) =
          zetaCompletedExplicitFormulaRightCenteredAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_shiftedRightPath_eq_affineLine F T t
    calc
      explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
                1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaArchimedeanLogDerivative z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
                  1 / 2))
          hpath
      _ =
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaRightAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
      _ = zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t := by
        exact Eq.refl _
  have hleft :
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t) := by
    funext t
    have hpath :
        zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
          zetaCompletedExplicitFormulaLeftAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine F T t
    have hshift :
        zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            (1 / 2 : ℂ) =
          zetaCompletedExplicitFormulaLeftCenteredAffineLine F t :=
      zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine F T t
    calc
      explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
                1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaArchimedeanLogDerivative z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
                  1 / 2))
          hpath
      _ =
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaArchimedeanLogDerivative
                (zetaCompletedExplicitFormulaLeftAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
      _ = zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t := by
        exact Eq.refl _
  exact congrArg₂ HSub.hSub
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hright)
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hleft)

/-- The scheduled archimedean vertical channel in named affine-kernel normal
form. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanVerticalChannel_eq_affineKernelIntegrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_eq_affineKernelIntegrals
      f F (h.height_schedule.height u)

/-- The scheduled archimedean vertical channel is the scheduled inverse-Gamma
completion channel minus the scheduled correction channel. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedean_eq_inverseGammaCompletion_sub_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F h u -
        zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
  let G : ℂ := zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T
  have hdecomp : G = A + C :=
    zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction
      f h.phi_control F T (h.height_schedule.avoids_boundary u)
  change A = G - C
  calc
    A = A + C - C := by
      exact (add_sub_cancel_right A C).symm
    _ = G - C := by
      exact congrArg (fun z : ℂ => z - C) hdecomp.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
