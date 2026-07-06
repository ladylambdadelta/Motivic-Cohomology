import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineIntegralZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleLeftStandardResidueValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion

/-!
# One-pole affine inversion transport

This file transports scheduled one-pole residue and off-pole limits to
whole-line affine-kernel integral values.
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

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrand_eq_affineKernel_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
  have hpath :
      zetaCompletedExplicitFormulaRightPath (F.rectangle T) t =
        zetaCompletedExplicitFormulaRightAffineLine F t :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_rightPath_eq
      F T t
  have hshift :
      zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - (1 / 2 : ℂ) =
        zetaCompletedExplicitFormulaRightCenteredAffineLine F t :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPole_verticalInversion_shiftedRightPath_eq
      F T t
  have hcoeff :
      -1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1) =
        -(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1)) :=
    neg_div (zetaCompletedExplicitFormulaRightAffineLine F t - 1) (1 : ℂ)
  calc
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      (-1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / (z - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
          hpath
    _ =
      (-1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1)) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
    _ =
      (-(1 / (zetaCompletedExplicitFormulaRightAffineLine F t - 1))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
          hcoeff
    _ = zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
        rfl

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrand_eq_affineKernel_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
  have hpath :
      zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
        zetaCompletedExplicitFormulaLeftAffineLine F t := by
    exact zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine F T t
  have hshift :
      zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - (1 / 2 : ℂ) =
        zetaCompletedExplicitFormulaLeftCenteredAffineLine F t := by
    exact zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine F T t
  have hcoeff :
      -1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1) =
        -(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1)) :=
    neg_div (zetaCompletedExplicitFormulaLeftAffineLine F t - 1) (1 : ℂ)
  calc
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      (-1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / (z - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          hpath
    _ =
      (-1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1)) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
    _ =
      (-(1 / (zetaCompletedExplicitFormulaLeftAffineLine F t - 1))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            z *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
          hcoeff
    _ = zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
        rfl

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrand_eq_affineKernel_ownerTransport
        f F T t
  exact
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hfun

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T =
      ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrand_eq_affineKernel_ownerTransport
        f F T t
  exact
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hfun

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelIntegral_tendsto_integral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)) := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
        f F h)

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelIntegral_tendsto_integral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)) := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
        f F h)

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_projection_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_projection_ownerOnePoleAffine
      f F h

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_projectionResidue_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c
  have hK_integral :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelIntegral_tendsto_integral_ownerTransport
      f F h
  have hleft_residue :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_projectionResidue_ownerLeftResidueValue
      f F h
  have hK_residue :
      Tendsto K atTop (𝓝 B) := by
    have hpoint :
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u)) =
        K := by
      funext u
      exact
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerTransport
          f F (h.height_schedule.height u)
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 B))
      hpoint
      hleft_residue
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      K
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
      B
      hK_integral
      hK_residue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
