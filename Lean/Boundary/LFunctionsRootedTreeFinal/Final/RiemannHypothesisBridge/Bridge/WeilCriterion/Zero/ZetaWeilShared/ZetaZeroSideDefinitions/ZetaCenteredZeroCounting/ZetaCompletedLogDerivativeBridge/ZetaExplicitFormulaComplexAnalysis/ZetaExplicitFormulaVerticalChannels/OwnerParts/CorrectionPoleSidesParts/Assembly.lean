import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSidesParts.AnalyticIntegrability

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
      exact Eq.refl _
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



end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
