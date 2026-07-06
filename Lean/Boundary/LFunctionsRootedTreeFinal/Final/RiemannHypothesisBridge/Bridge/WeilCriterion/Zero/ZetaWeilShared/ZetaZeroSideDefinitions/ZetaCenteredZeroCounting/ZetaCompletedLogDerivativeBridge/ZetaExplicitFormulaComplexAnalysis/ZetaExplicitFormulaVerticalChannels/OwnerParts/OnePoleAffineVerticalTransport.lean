import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels

/-!
# One-pole vertical-to-affine transport

This file owns the non-analytic change from the rectangle right vertical
one-pole integral to the corresponding affine-kernel interval integral.  It is
kept upstream of residue-tail and off-pole consumers so that quantitative tail
lemmas can use the transport without importing the downstream inversion file.
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

/-- Pointwise transport from the right one-pole vertical integrand on a
rectangle to the right one-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrand_eq_affineKernel_ownerOnePoleVerticalTransport
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

/-- Interval-integral transport from the right one-pole vertical rectangle
integral to the right one-pole affine-kernel interval integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
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
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegrand_eq_affineKernel_ownerOnePoleVerticalTransport
        f F T t
  exact
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hfun

/-- Pointwise transport from the left one-pole vertical integrand on a
rectangle to the left one-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrand_eq_affineKernel_ownerOnePoleVerticalTransport
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

/-- Interval-integral transport from the left one-pole vertical rectangle
integral to the left one-pole affine-kernel interval integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
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
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegrand_eq_affineKernel_ownerOnePoleVerticalTransport
        f F T t
  exact
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hfun

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
