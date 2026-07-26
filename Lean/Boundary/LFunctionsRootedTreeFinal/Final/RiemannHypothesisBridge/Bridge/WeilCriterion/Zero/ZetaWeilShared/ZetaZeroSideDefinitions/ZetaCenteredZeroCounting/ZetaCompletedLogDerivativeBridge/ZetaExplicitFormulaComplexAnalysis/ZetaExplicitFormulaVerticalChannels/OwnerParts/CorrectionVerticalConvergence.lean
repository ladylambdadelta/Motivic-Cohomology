import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionContribution
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleLocalCauchyValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.LeftZeroCancellation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleLeftStandardResidueValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.HorizontalEdgeBounds

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

/-- The right pole face transports to the one-sided `s = 0` Cauchy projection
plus the right one-pole projection value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_zeroPoleProjection_ownerCorrectionVertical
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
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_projection_directOffPoleCauchy
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
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
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
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
      (𝓝
        ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) := by
  let A : ℂ :=
    Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
      f.toZetaTestFunction' F.c +
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
        f * Complex.I
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A) := by
    unfold A
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_projectionResidue_ownerLeftOffPoleDecay
      f F h
  have hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) := by
    unfold B
    exact
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
          (A + B)) :=
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
      A + B =
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) := by
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I) +
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))))
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

/-- Projection cancellation for the corrected pole-face accounting. -/
theorem zetaCompletedExplicitFormulaCorrectionProjection_sub_leftProjectionResidue
    (P Q T B : ℂ) :
    (P + Q) - ((P + T) + (B + Q)) =
      -T - B := by
  have hleft :
      ((P + T) + (B + Q)) = ((P + T) + B) + Q := by
    exact (add_assoc (P + T) B Q).symm
  have hdrop :
      (P + Q) - (((P + T) + B) + Q) =
        P - ((P + T) + B) :=
    add_sub_add_right_eq_sub P ((P + T) + B) Q
  have hinner :
      P - (P + T) = -T := by
    calc
      P - (P + T) = P + -(P + T) := by
        exact sub_eq_add_neg P (P + T)
      _ = P + (-P + -T) := by
        exact congrArg (fun z : ℂ => P + z) (neg_add P T)
      _ = (P + -P) + -T := by
        exact (add_assoc P (-P) (-T)).symm
      _ = 0 + -T := by
        exact congrArg (fun z : ℂ => z + -T) (add_neg_cancel P)
      _ = -T := by
        exact zero_add (-T)
  have htail :
      P - ((P + T) + B) = -T - B := by
    calc
      P - ((P + T) + B) = P - (P + T) - B := by
        exact sub_add_eq_sub_sub P (P + T) B
      _ = -T - B := by
        exact congrArg (fun z : ℂ => z - B) hinner
  calc
    (P + Q) - ((P + T) + (B + Q)) =
        (P + Q) - (((P + T) + B) + Q) := by
      exact congrArg (fun z : ℂ => (P + Q) - z) hleft
    _ = P - ((P + T) + B) := by
      exact hdrop
    _ = -T - B := by
      exact htail

/-- Corrected projection accounting gives the same standard contour correction:
the right and left Cauchy projections cancel before the local tangent residue is
identified with the standard right zero-pole residue. -/
theorem zetaCompletedExplicitFormulaCorrectionProjectionResidue_sub_leftProjectionResidue_eq_standardContribution
    (f : ZetaAdmissibleFunction) (P Q : ℂ) :
    (P + Q) -
        ((P +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I + Q)) =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  let T : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
      f * Complex.I
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I
  let V : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f
  have hcancel :
      (P + Q) - ((P + T) + (B + Q)) =
        -T - B :=
    zetaCompletedExplicitFormulaCorrectionProjection_sub_leftProjectionResidue
      P Q T B
  have hT :
      -T = V := by
    unfold T
    unfold V
    exact
      (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq
        f).symm
  have hV :
      V =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) := by
    calc
      V =
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue
            f := by
        unfold V
        exact
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq_localVerticalResidue
            f).symm
      _ =
          -(((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) := by
        exact zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq f
  calc
    (P + Q) -
        ((P +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I + Q)) =
        (P + Q) - ((P + T) + (B + Q)) := by
      rfl
    _ = -T - B := by
      exact hcancel
    _ = V - B := by
      exact congrArg (fun z : ℂ => z - B) hT
    _ =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
          B := by
      exact congrArg (fun z : ℂ => z - B) hV
    _ =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
      rfl
    _ =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
      exact (zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f).symm

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
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
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
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_zeroPoleProjection_ownerCorrectionVertical
      f F h hone
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I) +
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :=
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
          ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
            ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
                f.toZetaTestFunction' F.c +
              zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
                f * Complex.I) +
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                  zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)))) :=
    Tendsto.sub hright hleft
  have htarget :
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) -
          ((Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I) +
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
                zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
    exact
      zetaCompletedExplicitFormulaCorrectionProjectionResidue_sub_leftProjectionResidue_eq_standardContribution
        f
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c)
        (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)
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
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
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
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hpointwise.symm
    hkernel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
