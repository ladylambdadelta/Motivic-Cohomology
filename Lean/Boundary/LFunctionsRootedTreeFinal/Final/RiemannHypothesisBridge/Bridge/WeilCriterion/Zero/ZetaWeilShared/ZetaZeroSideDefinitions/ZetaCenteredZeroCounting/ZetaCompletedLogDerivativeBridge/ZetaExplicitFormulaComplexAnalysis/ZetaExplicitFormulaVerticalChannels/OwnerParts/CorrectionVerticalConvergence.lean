import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionContribution
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversionEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.LeftZeroCancellation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleLeftStandardResidueValue

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

/-- The right pole face transports to the contour-side `s = 0` pole value plus
the right one-pole projection value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_zeroPoleProjectionValue_ownerCorrectionVertical
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_value_ownerChannelTransportAnalytic
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
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
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)))
    hpointwise.symm
    hsum

/-- The left pole face transports with the projection-corrected one-pole
residue normalization, consuming the non-circular one-pole left residue owner
theorem directly. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_projectionResidue_ownerCorrectionVertical
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
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
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_projectionResidue_ownerLeftResidueValue
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
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :=
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
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) =
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c :=
    zero_add ((((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)))
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

/-- Core correction-channel transport theorem in the standard-contour
normalization: the explicit two-pole vertical kernel converges to the
right-minus-left contour-side pole contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_standardContourContribution_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
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
      (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_zeroPoleProjectionValue_ownerCorrectionVertical
      f F h hone
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_projectionResidue_ownerCorrectionVertical
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
          ((zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :=
    Tendsto.sub hright hleft
  have htarget :
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
    have hzero :
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
          -(((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq f
    calc
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) =
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        calc
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                  zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
              =
              zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f -
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
            exact add_sub_add_right_eq_sub
              (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)
              (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
      _ =
          -(((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            z -
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
          hzero
      _ = zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
        exact (zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f).symm
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
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- Concrete correction-channel analytic transport with the standard-contour
single-pole normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
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
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaCorrectionPoleVerticalIntegral_tendsto_standardContourContribution_ownerChannelTransportAnalytic
      f F h hone
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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
