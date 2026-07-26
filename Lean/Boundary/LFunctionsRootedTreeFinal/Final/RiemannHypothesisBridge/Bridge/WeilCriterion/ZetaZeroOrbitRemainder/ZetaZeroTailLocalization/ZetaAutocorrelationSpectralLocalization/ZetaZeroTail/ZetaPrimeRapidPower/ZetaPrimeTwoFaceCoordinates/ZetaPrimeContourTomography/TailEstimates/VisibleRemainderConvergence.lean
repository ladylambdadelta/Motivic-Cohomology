import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.ConcreteResidueShadow
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.HorizontalContour.Owner

namespace Boundary
namespace LFunctions
noncomputable section
open Filter
open scoped Topology
namespace ZetaAdmissibleFunction

def completedPrimeContourTransportHorizontalDecayOrder_owner : ℕ :=
  0

noncomputable def completedPrimeContourTransportScheduleGeometry_owner :
    CompletedPrimeContourTransportScheduleGeometry where
  height_schedule := completedPrimeContourTransportHeightSchedule_owner
  horizontal_decay_order := completedPrimeContourTransportHorizontalDecayOrder_owner

noncomputable def completedPrimeContourTransportSummedTransport_owner
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    CompletedSummedPrimeContourTimeTransport f :=
  completedSummedPrimeContourTimeTransport_of_finiteWindowReconstruction f D

noncomputable def completedPrimeContourTransportSummedTransport_of_diagonalDebtCoordinate_re_hasSum_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (convolutionAutocorrelation f)))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index
                (ZetaAdmissibleFunction.reflect
                  (convolutionAutocorrelation f))))
    Creflect) :
    CompletedSummedPrimeContourTimeTransport f :=
  let htransport : CompletedSummedPrimeContourTimeTransport f :=
    completedPrimeContourTransportSummedTransport_owner f D
  let hleft : hhasSum = hhasSum :=
    Eq.refl hhasSum
  let hright : hhasSumReflect = hhasSumReflect :=
    Eq.refl hhasSumReflect
  Eq.ndrec
    (motive := fun proof =>
      CompletedSummedPrimeContourTimeTransport f)
    (Eq.ndrec
      (motive := fun proof =>
        CompletedSummedPrimeContourTimeTransport f)
      htransport
      hright)
    hleft

noncomputable def completedPrimeContourTransportScheduledFamily_owner
    (Dfamily : ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f) :
    CompletedPrimeContourTransportScheduledFamily where
  toCompletedPrimeContourTransportScheduleGeometry :=
    completedPrimeContourTransportScheduleGeometry_owner
  summedTransport :=
    fun f => completedPrimeContourTransportSummedTransport_owner f
      (Dfamily f)

noncomputable def completedPrimeContourTransportScheduledFamily_owner_of_envelopePolynomialBounds
    (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (Dfamily : ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hCpos : 0 ≤ Cpos) (hCneg : 0 ≤ Cneg)
    (henvpos : ∀ f : ZetaAdmissibleFunction, ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          f (canonicalZetaPaleyWienerSupportInterval f)
          index.center index.center ≤
        Cpos * ZetaPrimePowerIndex.polynomialHeightDecay kpos index)
    (henvneg : ∀ f : ZetaAdmissibleFunction, ∀ index : ZetaPrimePowerIndex,
      zetaPaleyWienerZeroOrderEnvelope
          (ZetaAdmissibleFunction.reflect f)
          (canonicalZetaPaleyWienerSupportInterval
            (ZetaAdmissibleFunction.reflect f))
          index.center index.center ≤
        Cneg * ZetaPrimePowerIndex.polynomialHeightDecay kneg index) :
    CompletedPrimeContourTransportScheduledFamily :=
  completedPrimeContourTransportScheduledFamily_owner
    Dfamily

theorem completedPrimeContourTransportScheduledFamily_owner_height_schedule :
    (Dfamily : ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f) →
    (completedPrimeContourTransportScheduledFamily_owner
        Dfamily).height_schedule =
      completedPrimeContourTransportHeightSchedule_owner :=
  fun Dfamily : ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f =>
    Eq.refl completedPrimeContourTransportHeightSchedule_owner

theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_concrete_of_height_schedule
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight : S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        S.height_schedule N f =
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f :=
  let hbase :
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          completedPrimeContourTransportHeightSchedule_owner N f =
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f :=
    Eq.refl (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
  Eq.subst
    (motive := fun heightSchedule :
        ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt heightSchedule N f =
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
    hheight.symm
    hbase

theorem completedPrimeContourTransportCoordinateRemainderTailAt_eq_concrete_of_height_schedule
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight : S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTailAt
        S.height_schedule N f =
      completedPrimeContourTransportCoordinateRemainderTail N f :=
  let hbase :
      completedPrimeContourTransportCoordinateRemainderTailAt
          completedPrimeContourTransportHeightSchedule_owner N f =
        completedPrimeContourTransportCoordinateRemainderTail N f :=
    Eq.refl (completedPrimeContourTransportCoordinateRemainderTail N f)
  Eq.subst
    (motive := fun heightSchedule :
        ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
      completedPrimeContourTransportCoordinateRemainderTailAt heightSchedule N f =
        completedPrimeContourTransportCoordinateRemainderTail N f)
    hheight.symm
    hbase

theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) :=
  let S : CompletedPrimeContourTransportScheduledFamily :=
    completedPrimeContourTransportScheduledFamily_owner Dfamily
  let hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner :=
    completedPrimeContourTransportScheduledFamily_owner_height_schedule Dfamily
  let hbox :
      Tendsto
        (fun N : ℕ =>
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_tendsto_zero_ownerTailEstimate
      S f hPhi hHorizontal
  let hfun :
      (fun N : ℕ =>
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          S.height_schedule N f) =
        fun N : ℕ =>
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f :=
    funext
      (fun N : ℕ =>
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_concrete_of_height_schedule
          S hheight N f)
  let hboxConcrete :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun stream : ℕ → ℝ => Tendsto stream atTop (𝓝 0))
      hfun
      hbox
  let hnorm :
      Tendsto
        (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    hboxConcrete.norm
  let hzero : ‖(0 : ℝ)‖ = 0 :=
    norm_zero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
        atTop
        (𝓝 value))
    hzero
    hnorm

theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_owner
    f Dfamily hmajorantFamily
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem completedPrimeContourTransportCoordinateRemainderTail_norm_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ => ‖completedPrimeContourTransportCoordinateRemainderTail N f‖)
      atTop
      (𝓝 0) :=
  let S : CompletedPrimeContourTransportScheduledFamily :=
    completedPrimeContourTransportScheduledFamily_owner Dfamily
  let hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner :=
    completedPrimeContourTransportScheduledFamily_owner_height_schedule Dfamily
  let htail :
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero_ownerTailEstimate
      S f hPhi hHorizontal
  let hfun :
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f) =
        fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTail N f :=
    funext
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt_eq_concrete_of_height_schedule
          S hheight N f)
  let htailConcrete :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun stream : ℕ → ℝ => Tendsto stream atTop (𝓝 0))
      hfun
      htail
  let hnorm :
      Tendsto
        (fun N : ℕ => ‖completedPrimeContourTransportCoordinateRemainderTail N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    htailConcrete.norm
  let hzero : ‖(0 : ℝ)‖ = 0 :=
    norm_zero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => ‖completedPrimeContourTransportCoordinateRemainderTail N f‖)
        atTop
        (𝓝 value))
    hzero
    hnorm

theorem completedPrimeContourTransportCoordinateRemainderTail_norm_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ => ‖completedPrimeContourTransportCoordinateRemainderTail N f‖)
      atTop
      (𝓝 0) :=
  completedPrimeContourTransportCoordinateRemainderTail_norm_tendsto_zero_owner
    f Dfamily hmajorantFamily
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) :=
  let hnorm :
      Tendsto
        (fun N : ℕ => ‖completedPrimeContourTransportCoordinateRemainderTail N f‖)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTail_norm_tendsto_zero_owner
      f Dfamily hmajorantFamily hPhi hHorizontal
  let hbound :
      ∀ᶠ N in atTop,
        ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ ≤
          ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ :=
    Eventually.of_forall (fun N : ℕ => le_rfl)
  squeeze_zero_norm' hbound hnorm

theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) :=
  completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_owner
    f Dfamily hmajorantFamily
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_of_coordinateRemainderTail
    f
    (completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_owner
      f Dfamily hmajorantFamily hPhi hHorizontal)

theorem finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (Dfamily : ∀ g : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction g)
    (hmajorantFamily : ∀ g : ZetaAdmissibleFunction,
      Summable (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation g)))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_owner
    f Dfamily hmajorantFamily
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem sampledHorizontalDifferenceComplex_tendsto_zero_of_edges
    (f : ZetaAdmissibleFunction)
    (htop :
      Tendsto
        (fun N : ℕ => sampledHorizontalTopIntegral N f)
        atTop
        (𝓝 0))
    (hbottom :
      Tendsto
        (fun N : ℕ => sampledHorizontalBottomIntegral N f)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f)
      atTop
      (𝓝 0) :=
  let hsub :
      Tendsto
        (fun N : ℕ =>
          sampledHorizontalTopIntegral N f -
            sampledHorizontalBottomIntegral N f)
        atTop
        (𝓝 (0 - 0)) :=
    htop.sub hbottom
  let hzero : (0 : ℂ) - 0 = 0 :=
    sub_zero 0
  let hfun :
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f) =
        fun N : ℕ =>
          sampledHorizontalTopIntegral N f -
            sampledHorizontalBottomIntegral N f :=
    funext
      (fun N : ℕ => sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f)
  Eq.subst
    (motive := fun u : ℕ → ℂ => Tendsto u atTop (𝓝 0))
    hfun.symm
    (Eq.subst
      (motive := fun limit : ℂ =>
        Tendsto
          (fun N : ℕ =>
            sampledHorizontalTopIntegral N f -
              sampledHorizontalBottomIntegral N f)
          atTop
          (𝓝 limit))
      hzero
      hsub)

theorem explicitFormulaFamilyHorizontalResidueWindowError_eq_sampledHorizontalDifferenceComplex
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    explicitFormulaFamilyHorizontalResidueWindowError
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)) =
      sampledHorizontalDifferenceComplex N f :=
  Eq.refl
    (explicitFormulaFamilyHorizontalResidueWindowError
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))

theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height u))
      atTop
      (𝓝 0) :=
  let S : CompletedPrimeContourTransportScheduleGeometry :=
    completedPrimeContourTransportScheduleGeometry_owner
  let hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner :=
    Eq.refl completedPrimeContourTransportHeightSchedule_owner
  let hsched :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (S.height_schedule.height u))
        atTop
        (𝓝 0) :=
    let h :
        ExplicitFormulaScheduledFamilyAnalyticPackage
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily :=
      completedPrimeContourTransportScheduledFamilyAnalyticPackage
        S
        f
        hPhi
        hHorizontal
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_scheduledPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      h
      S.horizontal_decay_order
  let hfun :
      (fun u : ℝ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (S.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height u)) :=
    congrArg
      (fun schedule : ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
        fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (schedule.height u))
      hheight
  Eq.subst
    (motive := fun v : ℝ → ℂ => Tendsto v atTop (𝓝 0))
    hfun
    hsched

theorem sampledHorizontalDifferenceComplex_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f)
      atTop
      (𝓝 0) :=
  let hcomplex :
      Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))
        atTop
        (𝓝 0) :=
    (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_scheduled_owner
      f hPhi hHorizontal).comp tendsto_natCast_atTop_atTop
  let hfun :
      (fun N : ℕ => sampledHorizontalDifferenceComplex N f) =
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) :=
    funext
      (fun N : ℕ =>
        (explicitFormulaFamilyHorizontalResidueWindowError_eq_sampledHorizontalDifferenceComplex
          N f).symm)
  Eq.subst
    (motive := fun u : ℕ → ℂ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hcomplex

theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))
      atTop
      (𝓝 0) :=
  let hsample :
      Tendsto
        (fun N : ℕ => sampledHorizontalDifferenceComplex N f)
        atTop
        (𝓝 0) :=
    sampledHorizontalDifferenceComplex_tendsto_zero_owner f
      hPhi hHorizontal
  let hfun :
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) =
        (fun N : ℕ => sampledHorizontalDifferenceComplex N f) :=
    funext
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError_eq_sampledHorizontalDifferenceComplex
          N f)
  Eq.subst
    (motive := fun u : ℕ → ℂ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hsample

theorem explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ =>
        explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))
      atTop
      (𝓝 0) :=
  explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_owner
    f
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem finitePrimeHorizontalResidueShadow_tendsto_zero_of_horizontalResidueWindowError
    (f : ZetaAdmissibleFunction)
    (herror :
      Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ)))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  let hre :
      Tendsto
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))))
        atTop
        (𝓝 (Complex.re 0)) :=
    (Complex.continuous_re.tendsto (0 : ℂ)).comp herror
  let hzero : Complex.re (0 : ℂ) = 0 :=
    Complex.zero_re
  Eq.subst
    (motive := fun limit : ℝ =>
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 limit))
    hzero
    (Eq.subst
      (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 (Complex.re 0)))
      (funext
        (fun N : ℕ =>
          (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
            N f).symm))
      hre)

theorem finitePrimeHorizontalResidueShadow_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        completedPrimeContourTransportHeightSchedule_owner) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueShadow_tendsto_zero_of_horizontalResidueWindowError
    f
    (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_owner
      f hPhi hHorizontal)

theorem finitePrimeHorizontalResidueShadow_tendsto_zero_of_concreteFactorData_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        completedPrimeContourTransportScheduleGeometry_owner) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueShadow_tendsto_zero_owner
    f
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_subResidueShadow_addResidueShadow
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) =
      fun N : ℕ =>
        (finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f) +
          finitePrimeHorizontalResidueShadow N f :=
  funext
    (fun N : ℕ =>
      (sub_add_cancel
        (finitePrimeContourTransportCoordinateRemainderWindow N f)
        (finitePrimeHorizontalResidueShadow N f)).symm)

theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_owner
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTraceReconstruction
    f D

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
