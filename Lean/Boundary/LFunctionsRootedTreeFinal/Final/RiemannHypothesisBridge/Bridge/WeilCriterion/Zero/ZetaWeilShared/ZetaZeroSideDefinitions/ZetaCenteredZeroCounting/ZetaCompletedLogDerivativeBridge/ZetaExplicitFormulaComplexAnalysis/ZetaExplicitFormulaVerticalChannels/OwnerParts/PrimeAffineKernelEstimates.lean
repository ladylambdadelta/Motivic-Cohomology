import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightVonMangoldtInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion

/-!
# Prime affine-kernel estimates

This file owns the affine-prime kernel estimates used by the scheduled prime
channel: right von Mangoldt exhaustion, left logarithmic-derivative exhaustion,
and the transport wrappers that turn separately proved whole-line values into
scheduled limits.  The right von Mangoldt inversion itself lands at the
one-sided natural contribution; the full public prime contribution requires the
complement branch recorded in `PrimeLogDerivativeTransport`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped LSeries.notation
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Strong measurability of the right von Mangoldt affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_aestronglyMeasurable_ownerInversion
    f F h

/-- Bundled majorant package for the right von Mangoldt affine kernel.  The analytic
content is polynomial/logarithmic control of the von Mangoldt Dirichlet-series
factor combined with rapid decay of `Φ_f`. -/
def zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F) :=
  zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage_ownerInversion
    f F h

/-- Existential majorant package for the right von Mangoldt affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage
    f F h).exists_majorant

/-- Integrability of the right von Mangoldt affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_majorantPackage
    f F h).integrable

/-- Symmetric-window convergence of the right von Mangoldt affine kernel to its
actual whole-line integral.  This isolates measure-theoretic exhaustion from
the separate Dirichlet-series/prime-distribution value theorem. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_symmetric
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
        f F h)

/-- Rectangle-window convergence of the right von Mangoldt affine kernel to its
actual whole-line integral. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_symmetric
        f F h)

/-- Scheduled-window convergence of the right von Mangoldt affine kernel to its
actual whole-line integral. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral_unscheduled
      f F h
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Direct symmetric-window right von Mangoldt convergence from a separately
proved prime-distribution value theorem. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_symmetric_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
        f F h)
      hvalue

/-- Rectangle-window right von Mangoldt convergence from a separately proved
prime-distribution value theorem. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_unscheduled_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F)
      (zetaCompletedExplicitFormulaPrimeContribution f)
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_symmetric_of_integral_eq
        f F h hvalue)

/-- Scheduled right von Mangoldt convergence from a separately proved
prime-distribution value theorem. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
        zetaCompletedExplicitFormulaPrimeContribution f) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_primeContribution_unscheduled_of_integral_eq
      f F h hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaPrimeContribution f)
      hkernel
      h.height_schedule.cofinal

/-- The whole-line right von Mangoldt affine-kernel value follows from an
independent scheduled prime-distribution value theorem.  This isolates the
uniqueness-of-limit assembly step from the later Dirichlet-series inversion
proof. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeContribution_of_scheduled_tendsto_primeContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t) =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  have hintegral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
        atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernelIntegral_tendsto_integral
      f F h
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeContribution f)
      hintegral
      hscheduled

/-- Under the parameter-level Gamma-regularity condition, the left prime
logarithmic-derivative affine kernel is strongly measurable. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_aestronglyMeasurable_of_gammaRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_aestronglyMeasurable_of_gammaRegular
    F hregular).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- A completed-zeta logarithmic-derivative bound and an inverse-Gamma
logarithmic-derivative bound combine to bound the left prime logarithmic
derivative factor. -/
theorem zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_factor_bound_of_completed_and_inverseGamma
    (F : ExplicitFormulaContourFamily)
    (BZ BG : ℝ)
    (hBZ_nonneg : 0 ≤ BZ)
    (hBG_nonneg : 0 ≤ BG)
    (hcompleted_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BZ * (1 + ‖t‖))
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ∀ t : ℝ,
      ‖explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        (BZ + BG) * (1 + ‖t‖) := by
  intro t
  let Z : ℂ :=
    completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let G : ℂ :=
    inverseGammaCompletionLogDeriv
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
  have hdef :
      explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        Z - G :=
    Eq.refl _
  have htriangle :
      ‖explicitFormulaPrimeLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        ‖Z‖ + ‖G‖ := by
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ ‖Z‖ + ‖G‖)
        hdef.symm
        (norm_sub_le Z G)
  have hsum :
      ‖Z‖ + ‖G‖ ≤
        BZ * (1 + ‖t‖) + BG * (1 + ‖t‖) :=
    add_le_add (hcompleted_bound t) (hinverseGamma_bound t)
  have hfactor :
      BZ * (1 + ‖t‖) + BG * (1 + ‖t‖) =
        (BZ + BG) * (1 + ‖t‖) :=
    (add_mul BZ BG (1 + ‖t‖)).symm
  exact htriangle.trans (hsum.trans_eq hfactor)

/-- The completed logarithmic derivative is linearly bounded on the right
affine line by the right von Mangoldt absolute-convergence bound and the
Gamma/Binet inverse-Gamma bound. -/
theorem zetaCompletedExplicitFormula_completedZetaNegLogDeriv_rightAffineLine_bound_of_gammaBinet
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) :=
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      F with
  | ⟨BG, hBG_nonneg, hG_bound⟩ =>
      let BP : ℝ :=
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F
      let B : ℝ := BP + BG
      have hBP_nonneg : 0 ≤ BP :=
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg F
      have hB_nonneg : 0 ≤ B :=
        add_nonneg hBP_nonneg hBG_nonneg
      have hbound :
          ∀ t : ℝ,
            ‖completedZetaNegLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
              B * (1 + ‖t‖) := by
        intro t
        let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
        let P : ℂ := explicitFormulaPrimeLogDerivative s
        let G : ℂ := inverseGammaCompletionLogDeriv s
        let Z : ℂ := completedZetaNegLogDeriv s
        have hprime_norm_eq :
            ‖P‖ =
              ‖(L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t)‖ :=
          (congrArg
            (fun z : ℂ => ‖z‖)
            (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
              F t)).symm
        have hprime_raw :
            ‖(L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤ BP :=
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_norm_le_factorBound_owner
            F t
        have hprime_constant : ‖P‖ ≤ BP :=
          hprime_norm_eq.trans_le hprime_raw
        have hprime_bound : ‖P‖ ≤ BP * (1 + ‖t‖) := by
          have hscale : BP ≤ BP * (1 + ‖t‖) := by
            calc
              BP = BP * 1 := by
                exact (mul_one BP).symm
              _ ≤ BP * (1 + ‖t‖) := by
                exact mul_le_mul_of_nonneg_left
                  (Real.one_le_one_add_norm t)
                  hBP_nonneg
          exact hprime_constant.trans hscale
        have hZ_eq : Z = P + G := by
          have hprime_def : P = Z - G :=
            show explicitFormulaPrimeLogDerivative s =
              completedZetaNegLogDeriv s - inverseGammaCompletionLogDeriv s from
              Eq.refl _
          calc
            Z = (Z - G) + G := by
              exact (sub_add_cancel Z G).symm
            _ = P + G := by
              exact congrArg (fun z : ℂ => z + G) hprime_def.symm
        have htriangle : ‖Z‖ ≤ ‖P‖ + ‖G‖ := by
          exact
            Eq.subst
              (motive := fun z : ℂ => ‖z‖ ≤ ‖P‖ + ‖G‖)
              hZ_eq.symm
              (norm_add_le P G)
        have hsum :
            ‖P‖ + ‖G‖ ≤
              BP * (1 + ‖t‖) + BG * (1 + ‖t‖) :=
          add_le_add hprime_bound (hG_bound t)
        have hfactor :
            BP * (1 + ‖t‖) + BG * (1 + ‖t‖) =
              B * (1 + ‖t‖) :=
          (add_mul BP BG (1 + ‖t‖)).symm
        exact htriangle.trans (hsum.trans_eq hfactor)
      ⟨B, hB_nonneg, hbound⟩

/- The right-line Dirichlet estimate is also a bound for the finite zeta-side
factor, after the explicit regular-domain normalization bridge. -/
theorem zetaCompletedExplicitFormula_zetaSideNegLogDeriv_rightAffineLine_bound_of_factorBound
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖zetaSideNegLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  let B : ℝ := zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound F
  have hB : 0 ≤ B :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactorBound_nonneg F
  refine ⟨B, hB, ?_⟩
  intro t
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  have hside : zetaSideNegLogDeriv s = explicitFormulaPrimeLogDerivative s :=
    zetaSideNegLogDeriv_eq_explicitFormulaPrimeLogDerivative_of_regular
      s
      (zetaCompletedExplicitFormulaRightAffineLine_ne_zero F t)
      (zetaCompletedExplicitFormulaRightAffineLine_ne_one F t)
      (zetaCompletedExplicitFormulaRightAffineLine_completedRiemannZeta_ne_zero F t)
      (zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_ne_zero F t)
  have hprime : ‖explicitFormulaPrimeLogDerivative s‖ ≤ B := by
    have hnorm :
        ‖explicitFormulaPrimeLogDerivative s‖ =
          ‖(L ↗Λ) (zetaCompletedExplicitFormulaRightAffineLine F t)‖ :=
      congrArg norm
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_eq_logDerivative
          F t)
    exact hnorm.trans_le
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_norm_le_factorBound_owner
        F t)
  have hscale : B ≤ B * (1 + ‖t‖) := by
    calc
      B = B * 1 := (mul_one B).symm
      _ ≤ B * (1 + ‖t‖) :=
        mul_le_mul_of_nonneg_left (Real.one_le_one_add_norm t) hB
  have hnormside :
      ‖zetaSideNegLogDeriv s‖ = ‖explicitFormulaPrimeLogDerivative s‖ :=
    congrArg norm hside
  exact hnormside.trans (hprime.trans hscale)

/- The left finite-factor normalization is transported on the canonical
Gamma-regular branch from the already-proved explicit-prime estimate. -/
theorem zetaCompletedExplicitFormula_zetaSideNegLogDeriv_leftAffineLine_bound_of_primeBound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ) (hbound : ∀ t : ℝ,
      ‖explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        B * (1 + ‖t‖)) :
    ∀ t : ℝ,
      ‖zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        B * (1 + ‖t‖) := by
  intro t
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  have hside : zetaSideNegLogDeriv s = explicitFormulaPrimeLogDerivative s :=
    zetaSideNegLogDeriv_eq_explicitFormulaPrimeLogDerivative_of_regular
      s
      (zetaCompletedExplicitFormulaLeftAffineLine_ne_zero F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_ne_one F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_completedRiemannZeta_ne_zero F t)
      (zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_ne_zero_of_gammaRegular
        F hregular t)
  have hnormside :
      ‖zetaSideNegLogDeriv s‖ = ‖explicitFormulaPrimeLogDerivative s‖ :=
    congrArg norm hside
  exact hnormside.trans (hbound t)

/-- A polynomial bound for the prime logarithmic derivative on the left affine
line packages the left prime affine kernel.  This theorem owns the
vertical-channel multiplication with the rapidly decaying test transform; the
logarithmic-derivative owner layer supplies the factor bound. -/
def zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_bound :
      ∀ t : ℝ,
        ‖explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℤ)))
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
        Nat.cast_one
    have htwo_lt_three : (2 : ℝ) < 3 := by
      have htwo_add_one : (2 : ℝ) + 1 = 3 :=
        two_add_one_eq_three
      exact Eq.subst
        (motive := fun value : ℝ => (2 : ℝ) < value)
        htwo_add_one
        (lt_add_of_pos_right 2 zero_lt_one)
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two htwo_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ))))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ)))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        Eq.trans
          (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
          (congrArg
            (fun exponent : ℝ => (1 + ‖t‖) ^ exponent)
            (Int.cast_neg 3))
      exact congrArg (fun x : ℝ => B * (C * x)) hpow
    exact Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hfun.symm
      hscaled
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_aestronglyMeasurable_of_gammaRegular
      F hregular
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        let weight : ℝ := (1 + ‖t‖) ^ (-(3 : ℤ))
        have hfactor :
            ‖explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
              B * (1 + ‖t‖) :=
          hfactor_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖explicitFormulaPrimeLogDerivative
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (Real.one_le_one_add_norm t))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ (1 : ℤ) *
                  (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              exact congrArg
                (fun x : ℝ => x * (1 + ‖t‖) ^ (-(4 : ℤ)))
                (zpow_one (1 + ‖t‖)).symm
            _ =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * (C * (1 + ‖t‖) ^ (-(3 : ℤ))) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * (C * (a * b)) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact
                  congrArg (fun x : ℝ => B * (x * b))
                    (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
          have hrewrite :
              a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * (C * x)) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- Completed-zeta and inverse-Gamma fixed-line bounds package the left prime
affine kernel. -/
def zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_completed_and_inverseGamma_bounds
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (BZ BG : ℝ)
    (hBZ_nonneg : 0 ≤ BZ)
    (hBG_nonneg : 0 ≤ BG)
    (hcompleted_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BZ * (1 + ‖t‖))
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F) := by
  have hsum_nonneg : 0 ≤ BZ + BG :=
    add_nonneg hBZ_nonneg hBG_nonneg
  have hfactor_bound :
      ∀ t : ℝ,
        ‖explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          (BZ + BG) * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaPrimeLogDerivative_leftAffineLine_factor_bound_of_completed_and_inverseGamma
      F BZ BG hBZ_nonneg hBG_nonneg hcompleted_bound hinverseGamma_bound
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_factor_bound
      f F h hregular (BZ + BG) hsum_nonneg hfactor_bound

/-- A zero-excised strip carrier for the whole left affine line supplies the
completed-zeta logarithmic-derivative side of the left prime factor bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_zeroExcisedLine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier) :
    ∀ t : ℝ,
      ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        h.logderiv_control.zeroExcisedStripBoundConstant
            (1 - F.c) (1 - F.c) E 1 *
          (1 + ‖t‖) := by
  intro t
  let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let BZ : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (1 - F.c) (1 - F.c) E 1
  have hraw :
      ‖completedZetaNegLogDeriv z‖ ≤
        BZ * (1 + ‖z.im‖) ^ (1 : ℕ) :=
    h.logderiv_control.zeroExcisedStripBoundConstant_bound
      (1 - F.c) (1 - F.c) E 1 z (hline_mem t)
  have him : z.im = t :=
    zetaCompletedExplicitFormulaLeftAffineLine_im F t
  have hnorm_im : ‖z.im‖ = ‖t‖ :=
    congrArg norm him
  have hbase :
      1 + ‖z.im‖ = 1 + ‖t‖ :=
    congrArg (fun x : ℝ => 1 + x) hnorm_im
  have hpow :
      (1 + ‖z.im‖) ^ (1 : ℕ) = 1 + ‖t‖ := by
    exact Eq.trans
      (pow_one (1 + ‖z.im‖))
      hbase
  exact
    hraw.trans_eq
      (congrArg (fun x : ℝ => BZ * x) hpow)

/-- The punctured left affine zero-excised carrier supplies the completed-zeta
logarithmic-derivative bound away from central height. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_off_central
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ t : ℝ,
      t ≠ 0 →
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          h.logderiv_control.zeroExcisedStripBoundConstant
              (1 - F.c) (1 - F.c)
              (zetaCompletedExplicitFormulaLeftAffineLinePuncturedZeroExcisedStrip F)
              1 *
            (1 + ‖t‖) := by
  intro t ht
  let E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c) :=
    zetaCompletedExplicitFormulaLeftAffineLinePuncturedZeroExcisedStrip F
  let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let BZ : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (1 - F.c) (1 - F.c) E 1
  have hmem : z ∈ E.carrier :=
    zetaCompletedExplicitFormulaLeftAffineLine_mem_puncturedZeroExcisedStrip
      F ht
  have hraw :
      ‖completedZetaNegLogDeriv z‖ ≤
        BZ * (1 + ‖z.im‖) ^ (1 : ℕ) :=
    h.logderiv_control.zeroExcisedStripBoundConstant_bound
      (1 - F.c) (1 - F.c) E 1 z hmem
  have him : z.im = t :=
    zetaCompletedExplicitFormulaLeftAffineLine_im F t
  have hnorm_im : ‖z.im‖ = ‖t‖ :=
    congrArg norm him
  have hbase :
      1 + ‖z.im‖ = 1 + ‖t‖ :=
    congrArg (fun x : ℝ => 1 + x) hnorm_im
  have hpow :
      (1 + ‖z.im‖) ^ (1 : ℕ) = 1 + ‖t‖ := by
    exact Eq.trans
      (pow_one (1 + ‖z.im‖))
      hbase
  exact
    hraw.trans_eq
      (congrArg (fun x : ℝ => BZ * x) hpow)

/-- A vertically regular contour supplies the whole-line completed-zeta
logarithmic-derivative bound on the left affine line. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_verticallyRegular
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    ∀ t : ℝ,
      ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t)‖ ≤
        h.logderiv_control.zeroExcisedStripBoundConstant
            (1 - F.toContourFamily.c) (1 - F.toContourFamily.c)
            (zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
              F)
            1 *
          (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_zeroExcisedLine
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
        F)
      (zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular
        F)

/-- A whole-line zero-excised carrier plus a linear inverse-Gamma factor bound
package the left prime affine kernel.  This is the honest owner-level form for
whole-line left affine estimates: the zero-excised carrier and Gamma regularity
are explicit hypotheses rather than implicit contour-family fields. -/
def zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F) := by
  let BZ : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (1 - F.c) (1 - F.c) E 1
  have hBZ_pos : 0 < BZ :=
    h.logderiv_control.zeroExcisedStripBoundConstant_pos
      (1 - F.c) (1 - F.c) E 1
  have hBZ_nonneg : 0 ≤ BZ :=
    le_of_lt hBZ_pos
  have hcompleted_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BZ * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_zeroExcisedLine
      f F h E hline_mem
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_completed_and_inverseGamma_bounds
      f F h hregular BZ BG hBZ_nonneg hBG_nonneg hcompleted_bound
      hinverseGamma_bound

/-- Existential majorant for the left prime affine kernel from the honest
whole-line hypotheses: a zero-excised carrier for the left affine line, Gamma
regularity, and a linear inverse-Gamma factor bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrableMajorant_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_zeroExcisedLine_and_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound).exists_majorant

/-- Integrability of the left prime affine kernel under the honest whole-line
zero-excision and inverse-Gamma factor-bound hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_zeroExcisedLine_and_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound).integrable

/-- Symmetric-window convergence of the left prime affine kernel to its
whole-line integral, under the honest whole-line majorant hypotheses.  This is
the convergence statement available before the separate contour-shift value
theorem identifies the integral with `0`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_symmetric_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_and_inverseGamma_bound
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)

/-- Rectangle-window convergence of the left prime affine kernel to its
whole-line integral under the honest whole-line majorant hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_unscheduled_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_symmetric_of_zeroExcisedLine_and_inverseGamma_bound
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)

/-- Scheduled rectangle-window convergence of the left prime affine kernel to
its whole-line integral under the honest whole-line majorant hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_of_zeroExcisedLine_and_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_integral_unscheduled_of_zeroExcisedLine_and_inverseGamma_bound
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Symmetric-window left prime logarithmic-derivative tail decay from the
honest whole-line majorant hypotheses and a separately proved zero-value
theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_symmetric_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      0
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_and_inverseGamma_bound
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)
      hvalue

/-- Rectangle-window left prime logarithmic-derivative tail decay from the
honest whole-line majorant hypotheses and a separately proved zero-value
theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_unscheduled_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      0
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_symmetric_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue)

/-- Scheduled left prime logarithmic-derivative tail decay from the honest
whole-line majorant hypotheses and a separately proved zero-value theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel :
      Tendsto K atTop (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_unscheduled_of_zeroExcisedLine_inverseGamma_bound_and_integral_eq_zero
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      0
      hkernel
      h.height_schedule.cofinal

/-- Existential majorant package for the left prime logarithmic-derivative
affine kernel from the honest whole-line zero-excision and inverse-Gamma
factor-bound hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrableMajorant_of_zeroExcisedLine_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t‖
            ≤ majorant t :=
  zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrableMajorant_of_zeroExcisedLine_and_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound

/-- Integrability of the left prime logarithmic-derivative affine kernel from
the honest whole-line zero-excision and inverse-Gamma factor-bound hypotheses. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_inverseGamma_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_zeroExcisedLine_and_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound

/-- Bundled majorant package for the left prime logarithmic-derivative affine kernel.
The analytic content is off-critical logarithmic-derivative growth combined
with rapid decay of `Φ_f` on the shifted left vertical line. -/
def zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F) :=
  zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_zeroExcisedLine_and_inverseGamma_bound
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound

/-- Existential majorant package for the left prime logarithmic-derivative
affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t‖
              ≤ majorant t :=
  (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound).exists_majorant

/-- Integrability of the left prime logarithmic-derivative affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage
    f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound).integrable

/- The left prime kernel has an owner-level integrability constructor that does
not consume the ambient strip log-derivative package.  Its completed factor is
transported from the right by the completed functional equation, while its
inverse-Gamma factor is supplied by the direct Binet estimate. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_owner_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      (volume : Measure ℝ) :=
  match
    zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_bound_of_gammaBinet
      F with
  | ⟨BZ, hBZ_nonneg, hcompleted_bound⟩ =>
      match
        zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
          F hregular with
      | ⟨BG, hBG_nonneg, hinverseGamma_bound⟩ =>
          (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_majorantPackage_of_completed_and_inverseGamma_bounds
            f F h hregular BZ BG hBZ_nonneg hBG_nonneg hcompleted_bound
            hinverseGamma_bound).integrable

/-- Vertically regular, Gamma-coherence-qualified integrability of the left
prime logarithmic-derivative affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_verticallyRegular_gammaBinetCoherence
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable_of_owner_gammaBinet
      f F.toContourFamily h hregular

/-- The whole-line left prime logarithmic-derivative affine-kernel tail value
follows from an independent scheduled tail-decay theorem.  The hypotheses are
exactly those needed for the exhaustion side of the argument. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
        atTop
        (𝓝 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
      0 := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      0
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)
      hscheduled

/-- Vertically regular whole-line left prime tail value from a separately
proved scheduled tail-decay theorem.  This is a backward compatibility
transport; the owner leaf is the whole-line zero value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_verticallyRegular_gammaBinet_scheduled_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
        f F.toContourFamily t) =
      0 := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
      F
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t ∈
          E.carrier :=
    zetaCompletedExplicitFormulaLeftAffineLine_mem_zeroExcisedStrip_of_verticallyRegular
      F
  let hdata :=
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
      F.toContourFamily hregular
  exact
    Exists.elim hdata
      (fun BG hBG_data =>
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero
          f F.toContourFamily h hregular E hline_mem
          BG hBG_data.1 hBG_data.2 hscheduled)

/-- Direct symmetric-window left prime logarithmic-derivative tail decay. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_symmetric
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      0
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integrable
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound)
      hvalue

/-- Unscheduled rectangle-window left prime logarithmic-derivative tail decay. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F)
      0
      (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_symmetric
        f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue)

/-- Scheduled kernel-level left prime logarithmic-derivative tail decay. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (E : CompletedZetaZeroExcisedStrip (1 - F.c) (1 - F.c))
    (hline_mem :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t ∈ E.carrier)
    (BG : ℝ)
    (hBG_nonneg : 0 ≤ BG)
    (hinverseGamma_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          BG * (1 + ‖t‖))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t)
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t
  have hkernel :
      Tendsto K atTop (𝓝 0) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernelIntegral_tendsto_zero_unscheduled
      f F h hregular E hline_mem BG hBG_nonneg hinverseGamma_bound hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      0
      hkernel
      h.height_schedule.cofinal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
