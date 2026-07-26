import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledZeroSide
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CompletedAffineContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Physical scheduled boundary limit

This file owns the package-native algebra from a raw scheduled vertical
right-minus-left limit to the normalized pole-corrected physical boundary
endpoint.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Scheduled analytic packages plus the physical boundary endpoint construct
the common-limit surface.  The zero-side endpoint is supplied by the
package-native scheduled residue owner chain. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_cleanScheduledPackageBoundaryLimit
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily_core
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
        f (hScheduled f))
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_scheduledPackage
        f
        (hScheduled f))
    boundaryLimit

/-- A scheduled analytic package plus its pole-corrected physical boundary
endpoint gives the exact Weil boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_cleanScheduledPackageBoundaryLimit_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_cleanScheduledPackageBoundaryLimit
      hScheduled
      boundaryLimit)

/-- The right rectangle path is the right affine line of the same contour family. -/
theorem zetaCompletedExplicitFormulaRightPath_rectangle_eq_rightAffineLine
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily) (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
        (family.rectangle T) t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
        family t :=
  Eq.refl _

/-- The left rectangle path is the left affine line of the same contour family. -/
theorem zetaCompletedExplicitFormulaLeftPath_rectangle_eq_leftAffineLine
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily) (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
        (family.rectangle T) t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
        family t :=
  Eq.refl _

/-- The elementary right affine centering algebra. -/
theorem zetaCompletedExplicitFormula_rightAffine_center_sub_algebra
    (a b : ℂ) :
    (a - (1 / 2 : ℂ)) + b = (a + b) - (1 / 2 : ℂ) :=
  let half : ℂ := (1 / 2 : ℂ)
  let hsubLeft :
      (a - half) + b = (a + (-half)) + b :=
    congrArg (fun value : ℂ => value + b) (sub_eq_add_neg a half)
  let hassocLeft :
      (a + (-half)) + b = a + ((-half) + b) :=
    add_assoc a (-half) b
  let hcomm :
      a + ((-half) + b) = a + (b + (-half)) :=
    congrArg (fun value : ℂ => a + value) (add_comm (-half) b)
  let hassocRight :
      a + (b + (-half)) = (a + b) + (-half) :=
    (add_assoc a b (-half)).symm
  let hsubRight :
      (a + b) + (-half) = (a + b) - half :=
    (sub_eq_add_neg (a + b) half).symm
  Eq.trans hsubLeft
    (Eq.trans hassocLeft
      (Eq.trans hcomm
        (Eq.trans hassocRight hsubRight)))

/-- The right centered affine line is the rectangle right path shifted by `1 / 2`. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_eq_rightPath_sub_half
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily) (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightCenteredAffineLine
        family t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
        (family.rectangle T) t - (1 / 2 : ℂ) :=
  let a : ℂ := family.c
  let b : ℂ := t * Complex.I
  let hcenter :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightCenteredAffineLine
          family t =
        (a - (1 / 2 : ℂ)) + b :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightCenteredAffineLine_eq
      family t
  let halgebra :
      (a - (1 / 2 : ℂ)) + b = (a + b) - (1 / 2 : ℂ) :=
    zetaCompletedExplicitFormula_rightAffine_center_sub_algebra a b
  let hpath :
      a + b =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
          (family.rectangle T) t :=
    (zetaCompletedExplicitFormulaRightPath_rectangle_eq_rightAffineLine
      family T t).symm
  Eq.trans hcenter
    (Eq.trans halgebra
      (congrArg (fun value : ℂ => value - (1 / 2 : ℂ)) hpath))

/-- The left centered affine line is the rectangle left path shifted by `1 / 2`. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_leftPath_sub_half
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily) (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
        family t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
        (family.rectangle T) t - (1 / 2 : ℂ) :=
  let a : ℂ := (1 : ℂ) - family.c
  let b : ℂ := t * Complex.I
  let hcenter :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
          family t =
        (a - (1 / 2 : ℂ)) + b :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq
      family t
  let halgebra :
      (a - (1 / 2 : ℂ)) + b = (a + b) - (1 / 2 : ℂ) :=
    zetaCompletedExplicitFormula_rightAffine_center_sub_algebra a b
  let hpath :
      a + b =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
          (family.rectangle T) t :=
    (zetaCompletedExplicitFormulaLeftPath_rectangle_eq_leftAffineLine
      family T t).symm
  Eq.trans hcenter
    (Eq.trans halgebra
      (congrArg (fun value : ℂ => value - (1 / 2 : ℂ)) hpath))

/-- The right affine kernel equals the right contour-line integrand pointwise. -/
theorem zetaCompletedRightAffineKernel_eq_rightLineIntegrand
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t =
      ZetaAdmissibleFunction.completedZetaNegLogDeriv
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
            (family.rectangle T) t) *
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
            (family.rectangle T) t - (1 / 2 : ℂ)) :=
  let hline :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
          family t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
          (family.rectangle T) t :=
    (zetaCompletedExplicitFormulaRightPath_rectangle_eq_rightAffineLine
      family T t).symm
  let hcenter :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightCenteredAffineLine
          family t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
          (family.rectangle T) t - (1 / 2 : ℂ) :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine_eq_rightPath_sub_half
      family T t
  calc
    ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t =
        ZetaAdmissibleFunction.completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
              family t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightCenteredAffineLine
              family t) := Eq.refl _
    _ =
        ZetaAdmissibleFunction.completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
              (family.rectangle T) t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
              (family.rectangle T) t - (1 / 2 : ℂ)) :=
      congrArg₂ HMul.hMul
        (congrArg ZetaAdmissibleFunction.completedZetaNegLogDeriv hline)
        (congrArg
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe)
          hcenter)

/-- The left affine kernel equals the left contour-line integrand pointwise. -/
theorem zetaCompletedLeftAffineKernel_eq_leftLineIntegrand
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (T t : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
      ZetaAdmissibleFunction.completedZetaNegLogDeriv
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
            (family.rectangle T) t) *
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
            (family.rectangle T) t - (1 / 2 : ℂ)) :=
  let hline :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
          family t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
          (family.rectangle T) t :=
    (zetaCompletedExplicitFormulaLeftPath_rectangle_eq_leftAffineLine
      family T t).symm
  let hcenter :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
          family t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
          (family.rectangle T) t - (1 / 2 : ℂ) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_leftPath_sub_half
      family T t
  calc
    ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
        ZetaAdmissibleFunction.completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
              family t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
              family t) := Eq.refl _
    _ =
        ZetaAdmissibleFunction.completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
              (family.rectangle T) t) *
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
              (family.rectangle T) t - (1 / 2 : ℂ)) :=
      congrArg₂ HMul.hMul
        (congrArg ZetaAdmissibleFunction.completedZetaNegLogDeriv hline)
        (congrArg
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe)
          hcenter)

/-- The affine channel is the raw right-minus-left vertical contour expression. -/
theorem zetaCompletedAffineVerticalChannel_eq_rightLineIntegral_sub_leftLineIntegral
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (T : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel probe family T =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
          probe (family.rectangle T) -
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
          probe (family.rectangle T) :=
  let rightIntegralEquality :
      (∫ t in Set.Icc (-(family.rectangle T).T) (family.rectangle T).T,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
          probe (family.rectangle T) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun t membership =>
        Eq.subst
          (motive := fun intervalMembership :
            t ∈ Set.Icc (-(family.rectangle T).T) (family.rectangle T).T =>
              ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t =
                ZetaAdmissibleFunction.completedZetaNegLogDeriv
                    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t) *
                  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
                    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t - (1 / 2 : ℂ)))
          (Eq.refl membership)
          (zetaCompletedRightAffineKernel_eq_rightLineIntegrand
            probe family T t))
  let leftIntegralEquality :
      (∫ t in Set.Icc (-(family.rectangle T).T) (family.rectangle T).T,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
          probe (family.rectangle T) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun t membership =>
        Eq.subst
          (motive := fun intervalMembership :
            t ∈ Set.Icc (-(family.rectangle T).T) (family.rectangle T).T =>
              ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
                ZetaAdmissibleFunction.completedZetaNegLogDeriv
                    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t) *
                  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
                    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t - (1 / 2 : ℂ)))
          (Eq.refl membership)
          (zetaCompletedLeftAffineKernel_eq_leftLineIntegrand
            probe family T t))
  congrArg₂ HSub.hSub rightIntegralEquality leftIntegralEquality

/-- Cofinal scheduled exhaustion of the completed affine vertical channel from
right and left affine-kernel integrability and the full-line value. -/
theorem zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (heightSchedule :
      ZetaAdmissibleFunction.ExplicitFormulaCofinalHeightSchedule family)
    (rightIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family)
        (volume : Measure ℝ))
    (valueEquality :
      (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t) =
          ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel probe) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          probe family (heightSchedule.height u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel probe)) :=
  let rightLimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle (heightSchedule.height u)).T)
              (family.rectangle (heightSchedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t)
        atTop
        (𝓝
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t)) :=
    ZetaAdmissibleFunction.explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family heightSchedule.height
      (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
      heightSchedule.cofinal rightIntegrable
  let leftLimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle (heightSchedule.height u)).T)
              (family.rectangle (heightSchedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)
        atTop
        (𝓝
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)) :=
    ZetaAdmissibleFunction.explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family heightSchedule.height
      (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family)
      heightSchedule.cofinal leftIntegrable
  let differenceLimit :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(family.rectangle (heightSchedule.height u)).T)
              (family.rectangle (heightSchedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
            ∫ t in Set.Icc
              (-(family.rectangle (heightSchedule.height u)).T)
              (family.rectangle (heightSchedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)
        atTop
        (𝓝
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)) :=
    rightLimit.sub leftLimit
  let functionEquality :
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(family.rectangle (heightSchedule.height u)).T)
            (family.rectangle (heightSchedule.height u)).T,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
          ∫ t in Set.Icc
            (-(family.rectangle (heightSchedule.height u)).T)
            (family.rectangle (heightSchedule.height u)).T,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t) =
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            probe family (heightSchedule.height u)) :=
    Eq.refl
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          probe family (heightSchedule.height u))
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel probe)))
    functionEquality
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (∫ t in Set.Icc
                (-(family.rectangle (heightSchedule.height u)).T)
                (family.rectangle (heightSchedule.height u)).T,
              ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
              ∫ t in Set.Icc
                (-(family.rectangle (heightSchedule.height u)).T)
                (family.rectangle (heightSchedule.height u)).T,
              ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)
          atTop
          (𝓝 target))
      valueEquality
      differenceLimit)

/-- A scheduled-package raw vertical boundary limit gives the package-native
normalized pole-corrected boundary endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_rawVerticalLimit
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (rawLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  let probe : ZetaAdmissibleFunction :=
    zetaAutocorrelationPhysicalProbe f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    zetaAutocorrelationPhysicalContourFamily f
  let poles : ℂ :=
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum probe
  let boundary : ℂ :=
    zetaCompletedAffinePhysicalBoundaryChannel probe
  let dividedLimit :
      Tendsto
        (fun u : ℝ =>
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u))) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi)
        atTop
        (𝓝
          ((ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi)) :=
    rawLimit.div_const ZetaAdmissibleFunction.explicitFormulaTwoPi
  let poleLimit :
      Tendsto (fun value : ℝ => poles) atTop (𝓝 poles) :=
    tendsto_const_nhds
  let correctedLimit :
      Tendsto
        (fun u : ℝ =>
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u))) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi -
          poles)
        atTop
        (𝓝
          ((ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
              ZetaAdmissibleFunction.explicitFormulaTwoPi -
            poles)) :=
    dividedLimit.sub poleLimit
  let divisionEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        boundary :=
    mul_div_cancel_left₀
      boundary
      ZetaAdmissibleFunction.explicitFormulaTwoPi_ne_zero
  let targetEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi - poles =
        zetaCompletedAffinePoleCorrectedBoundaryChannel probe :=
    Eq.trans
      (congrArg (fun value : ℂ => value - poles) divisionEquality)
      (zetaCompletedAffinePoleCorrectedBoundaryChannel_eq probe).symm
  let packageEquality :
      (fun u : ℝ =>
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              probe
              (family.rectangle (h.height_schedule.height u))) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi -
          poles) =
        zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h :=
    Eq.refl
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
        atTop
        (𝓝 target))
    targetEquality
    (Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop
          (𝓝
            ((ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
                ZetaAdmissibleFunction.explicitFormulaTwoPi -
              poles)))
      packageEquality
      correctedLimit)

/-- A scheduled-package completed affine-channel boundary limit gives the
package-native normalized pole-corrected boundary endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (channelLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            (h.height_schedule.height u))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  let rawFunctionEquality :
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u))) :=
    funext
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel_eq_rightLineIntegral_sub_leftLineIntegral
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          (h.height_schedule.height u))
  let rawLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
    Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f))))
      rawFunctionEquality
      channelLimit
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_rawVerticalLimit
    f h rawLimit

end
end LFunctions
end Boundary
