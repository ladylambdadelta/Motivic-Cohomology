import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities

/-!
# Right zero-pole Cauchy assembly

This file owns the algebraic and limit-theoretic assembly from a finite
zero-pole rectangle boundary value, left-face decay, and horizontal-edge decay
to the scheduled right-face Cauchy/Laplace inversion limit.
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

/-- A positive-height finite Cauchy equality for the `s = 0` rectangle boundary
gives the scheduled boundary-residue limit at an arbitrary value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_of_positiveHeight_boundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (K : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F T = K) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 K) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ => K) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  exact hevent.tendsto_iff.2 tendsto_const_nhds

/-- A positive-height finite Cauchy equality for the `s = 0` rectangle boundary
gives the scheduled centered boundary-residue limit. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F T =
            1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_of_positiveHeight_boundaryResidue_ownerAssembly
      f F h (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)
      hpositive

/-- Algebraic transport from the finite `s = 0` rectangle boundary residue
limit to the scheduled right zero-pole vertical channel, for an arbitrary
residue value.

The only analytic inputs are the left-face decay, the horizontal-edge decay,
and the finite-rectangle boundary residue. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_rectangleBoundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (K : ℂ)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 K) := by
  have hleft_minus_horizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 - 0)) :=
    hleft.sub hhorizontal
  have hboundaryK :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K) :=
    hboundary
  have hsum :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((0 - 0) + K)) :=
    hleft_minus_horizontal.add hboundaryK
  have hright_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u
    let C : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)
    have hC : C = R - L + H :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
        f F h u
    change R = (L - H) + C
    exact rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq R L H C hC
  have htarget :
      (0 - 0 : ℂ) + K = K := by
    calc
      (0 - 0 : ℂ) + K = (0 + -0 : ℂ) + K := by
        exact congrArg (fun z : ℂ => z + K) (sub_eq_add_neg 0 0)
      _ = (0 : ℂ) + K := by
        exact congrArg (fun z : ℂ => (0 + z : ℂ) + K) (neg_zero : -(0 : ℂ) = 0)
      _ = K := by
        exact zero_add K
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 K))
    hright_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Algebraic transport from the finite `s = 0` rectangle boundary residue
limit to the scheduled right zero-pole vertical channel.

The only analytic inputs are the left-face decay, the horizontal-edge decay,
and the centered finite-rectangle boundary residue. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_of_rectangleBoundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_rectangleBoundaryResidue_ownerAssembly
      f F h (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)
      hleft hhorizontal hboundary

/-- Tangent-contour transport from a finite zero-pole local residue value to
the real-parameter right vertical face.

The genuine contour boundary carries the vertical tangent factor `I`; hence a
tangent boundary residue value `B` gives the right real-side vertical value
`-(B * I)` once the left face and horizontal remainder vanish. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_tangentBoundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (B : ℂ)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(B * Complex.I))) := by
  let R : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  let C : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hleftI :
      Tendsto (fun u : ℝ => L u * Complex.I) atTop (𝓝 (0 * Complex.I)) :=
    hleft.mul tendsto_const_nhds
  have hleftI_zero :
      Tendsto (fun u : ℝ => L u * Complex.I) atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => L u * Complex.I) atTop (𝓝 z))
      (zero_mul Complex.I)
      hleftI
  have hleft_minus_horizontal :
      Tendsto
        (fun u : ℝ => L u * Complex.I - H u)
        atTop
        (𝓝 (0 - 0)) :=
    hleftI_zero.sub hhorizontal
  have hsum :
      Tendsto
        (fun u : ℝ => (L u * Complex.I - H u) + C u)
        atTop
        (𝓝 ((0 - 0) + B)) :=
    hleft_minus_horizontal.add htangent
  have hrightI_fun :
      (fun u : ℝ => R u * Complex.I) =
      (fun u : ℝ => (L u * Complex.I - H u) + C u) := by
    funext u
    have hC : C u = R u * Complex.I - L u * Complex.I + H u :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
        f F h u
    exact
      rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq
        (R u * Complex.I) (L u * Complex.I) (H u) (C u) hC
  have htarget :
      (0 - 0 : ℂ) + B = B := by
    calc
      (0 - 0 : ℂ) + B = (0 + -0 : ℂ) + B := by
        exact congrArg (fun z : ℂ => z + B) (sub_eq_add_neg 0 0)
      _ = (0 : ℂ) + B := by
        exact congrArg (fun z : ℂ => (0 + z : ℂ) + B) (neg_zero : -(0 : ℂ) = 0)
      _ = B := by
        exact zero_add B
  have hrightI :
      Tendsto (fun u : ℝ => R u * Complex.I) atTop (𝓝 B) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 B))
      hrightI_fun.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun u : ℝ => (L u * Complex.I - H u) + C u)
            atTop
            (𝓝 z))
        htarget
        hsum)
  have hnegI :
      Tendsto
        (fun u : ℝ => -((R u * Complex.I) * Complex.I))
        atTop
        (𝓝 (-(B * Complex.I))) :=
    (hrightI.mul tendsto_const_nhds).neg
  have hpoint :
      (fun u : ℝ => -((R u * Complex.I) * Complex.I)) = R := by
    funext u
    have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
      Complex.I_mul_I
    calc
      -((R u * Complex.I) * Complex.I) =
          -(R u * (Complex.I * Complex.I)) := by
        exact congrArg Neg.neg (mul_assoc (R u) Complex.I Complex.I)
      _ = -(R u * (-(1 : ℂ))) := by
        exact congrArg (fun z : ℂ => -(R u * z)) hI_sq
      _ = -(-R u) := by
        exact congrArg Neg.neg (mul_neg_one (R u))
      _ = R u := by
        exact neg_neg (R u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (-(B * Complex.I))))
    hpoint
    hnegI

/-- Tangent-contour transport specialized to the local `s = 0` residue
normalization.  This keeps the raw local Cauchy residue separate from the
centered correction-pole value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_localVerticalResidueValue_of_tangentBoundaryResidue_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f)) := by
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f
  have hraw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (-(B * Complex.I))) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_tangentBoundaryResidue_ownerAssembly
      f F h B hleft hhorizontal htangent
  have hvalue :
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f =
        -(B * Complex.I) := by
    exact zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq f
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 z))
    hvalue.symm
    hraw

/-- Scheduled right zero-pole face transport from a centered rectangle-boundary
hypothesis, left-face decay, and horizontal decay.

This theorem concludes the centered boundary value that its hypothesis
provides.  It does not identify that centered value with the contour-side
right zero-pole vertical inversion value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_centeredPolePhi_of_boundary_left_horizontal_ownerAssembly
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F T =
            1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) := by
  have hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue_ownerAssembly
      f F h hpositive
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_of_rectangleBoundaryResidue_ownerAssembly
      f F h hleft hhorizontal hboundary
  have hscheduled :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u) =
      fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_verticalIntegral
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)))
    hscheduled.symm
    hright

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
