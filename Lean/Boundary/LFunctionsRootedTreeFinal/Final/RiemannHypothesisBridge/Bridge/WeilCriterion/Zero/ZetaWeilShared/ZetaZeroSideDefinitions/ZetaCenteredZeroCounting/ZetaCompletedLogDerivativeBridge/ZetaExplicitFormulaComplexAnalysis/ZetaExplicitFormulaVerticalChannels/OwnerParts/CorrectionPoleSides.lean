import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.TransportProjection

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

/-- Pointwise normalization of the correction vertical channel to the explicit two-pole
kernel.  The sign here is inherited from
`explicitFormulaCorrectionLogDerivative_eq_poleCorrection`; the left side is subtracted
with the same orientation convention as the other vertical channels. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_eq_poleCorrectionVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
        (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
  have hright :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
  have hleft :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) =
        (fun t : ℝ =>
          (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
              1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    funext t
    exact congrArg
      (fun z : ℂ =>
        z * zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
  exact congrArg₂ HSub.hSub
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hright)
    (congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      hleft)

/-- The corrected contribution is the centered two-pole coefficient applied to the
test transform at the basepoint. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_eq_centeredPolePhi
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution f =
      (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
        zetaCompletedExplicitFormulaPhi f 0 := by
  exact zetaCompletedExplicitFormulaCorrectionContribution_eq f

/-- The right-face pole-correction vertical integral with the completed-pole kernel
written explicitly. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The left-face pole-correction vertical integral with the completed-pole kernel
written explicitly. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
        1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand of the right-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The `s = 1` summand of the right-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand of the left-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 1` summand of the left-face pole-correction vertical integral. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The `s = 0` summand on the top horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)

/-- The `s = 0` summand on the bottom horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)

/-- The `s = 1` summand on the top horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)

/-- The `s = 1` summand on the bottom horizontal side. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)

/-- The right-face `s = 1` correction integrand is the isolated kernel evaluated
on the right path. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
  rfl

/-- The left-face `s = 1` correction integrand is the isolated kernel evaluated
on the left path. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
  rfl

/-- The top-edge `s = 1` correction integrand is the isolated kernel evaluated
on the top path. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) :=
  rfl

/-- The bottom-edge `s = 1` correction integrand is the isolated kernel evaluated
on the bottom path. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) :=
  rfl

/-- The tangent-weighted right-side integral is the old real-side integral
multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted left-side integral is the old real-side integral
multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted top side is definitionally the old top horizontal
integral, since the top parametrization has tangent `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T :=
  rfl

/-- The tangent-weighted bottom side is definitionally the old bottom horizontal
integral before the final boundary orientation sign is applied. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T :=
  rfl

/-- The genuine `s = 1` contour boundary unfolds to the old four real-side
integrals with the missing vertical tangent factors restored. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T := by
  let RT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T
  let LT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T
  let TT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral f F T
  let BT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral f F T
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
  have hR : RT = R * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hL : LT = L * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hU : TT = U :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
      f F T
  have hB : BT = B :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        RT - LT + TT - BT := by
      rfl
    _ = R * Complex.I - LT + TT - BT := by
      exact congrArg (fun x : ℂ => x - LT + TT - BT) hR
    _ = R * Complex.I - L * Complex.I + TT - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - x + TT - BT) hL
    _ = R * Complex.I - L * Complex.I + U - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x - BT) hU
    _ = R * Complex.I - L * Complex.I + U - B := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + U - x) hB

/-- The isolated `s = 0` correction kernel as a function of the contour variable. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  (-1 / z) * zetaCompletedExplicitFormulaPhi f (z - 1 / 2)

/-- The tangent-weighted right side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted left side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) * Complex.I

/-- The tangent-weighted top side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)

/-- The tangent-weighted bottom side of the isolated `s = 0` correction contour. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x in Set.uIcc F.c (1 - F.c),
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)

/-- The genuine tangent-weighted rectangle contour integral for the isolated
`s = 0` correction kernel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T

/-- The tangent-weighted isolated `s = 0` rectangle boundary integral unfolds to
its four oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T :=
  rfl

/-- The right-face `s = 0` correction integrand is the isolated kernel evaluated
on the right path. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
  rfl

/-- The left-face `s = 0` correction integrand is the isolated kernel evaluated
on the left path. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
  rfl

/-- The top-edge `s = 0` correction integrand is the isolated kernel evaluated
on the top path. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) :=
  rfl

/-- The bottom-edge `s = 0` correction integrand is the isolated kernel evaluated
on the bottom path. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleIntegrand_eq_kernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) :=
  rfl

/-- The tangent-weighted right-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted left-side `s = 0` integral is the old real-side
integral multiplied by the vertical tangent `I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral_eq_vertical_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I :=
  integral_smul_const
    (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
    Complex.I

/-- The tangent-weighted top `s = 0` side is definitionally the old top
horizontal integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The tangent-weighted bottom `s = 0` side is definitionally the old bottom
horizontal integral before the final boundary orientation sign is applied. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The genuine `s = 0` contour boundary unfolds to the old four real-side
integrals with the missing vertical tangent factors restored. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T * Complex.I +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T := by
  let RT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T
  let LT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T
  let TT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral f F T
  let BT : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral f F T
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  have hR : RT = R * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hL : LT = L * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral_eq_vertical_mul_I
      f F T
  have hU : TT = U :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleTangentIntegral_eq_horizontal
      f F T
  have hB : BT = B :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleTangentIntegral_eq_horizontal
      f F T
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        RT - LT + TT - BT := by
      rfl
    _ = R * Complex.I - LT + TT - BT := by
      exact congrArg (fun x : ℂ => x - LT + TT - BT) hR
    _ = R * Complex.I - L * Complex.I + TT - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - x + TT - BT) hL
    _ = R * Complex.I - L * Complex.I + U - BT := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x - BT) hU
    _ = R * Complex.I - L * Complex.I + U - B := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + U - x) hB

/-- The oriented finite-rectangle boundary integral for the `s = 0` correction pole. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T

/-- The oriented finite-rectangle boundary integral for the `s = 1` correction pole. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T

/-- The `s = 0` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T :=
  rfl

/-- The `s = 1` finite-rectangle single-pole boundary integral unfolds to its four
oriented sides. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral f F T =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T :=
  rfl

/-- The scheduled `s = 0` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
              f F (h.height_schedule.height u) :=
  rfl

/-- The scheduled `s = 1` single-pole rectangle boundary integral is the four-side
identity at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
            f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) :=
  rfl

/-- Additive algebra for isolating the left side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    L = R + H - C := by
  have hsum : L + C = R + H := by
    calc
      L + C = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + x) hC
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L)
      _ = (L + (R + -L)) + H := by
        exact (add_assoc L (R + -L) H).symm
      _ = ((L + R) + -L) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc L R (-L))
      _ = ((R + L) + -L) + H := by
        exact congrArg (fun x : ℂ => (x + -L) + H) (add_comm L R)
      _ = (R + (L + -L)) + H := by
        exact congrArg (fun x : ℂ => x + H) (add_assoc R L (-L)).symm
      _ = (R + 0) + H := by
        exact congrArg (fun x : ℂ => (R + x) + H) (add_right_neg L)
      _ = R + H := by
        exact congrArg (fun x : ℂ => x + H) (add_zero R)
  exact
    (eq_sub_iff_add_eq.mpr hsum).symm

/-- Additive algebra for isolating the right side from an oriented rectangle boundary
identity `C = R - L + H`. -/
theorem rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq
    (R L H C : ℂ) (hC : C = R - L + H) :
    R = L - H + C := by
  have hsum : R + H = C + L := by
    calc
      R + H = R + (L + -L + H) := by
        exact congrArg (fun x : ℂ => R + (x + H)) (add_right_neg L).symm
      _ = R + (L + (-L + H)) := by
        exact congrArg (fun x : ℂ => R + x) (add_assoc L (-L) H)
      _ = (R + L) + (-L + H) := by
        exact (add_assoc R L (-L + H)).symm
      _ = (L + R) + (-L + H) := by
        exact congrArg (fun x : ℂ => x + (-L + H)) (add_comm R L)
      _ = L + (R + (-L + H)) := by
        exact add_assoc L R (-L + H)
      _ = L + ((R + -L) + H) := by
        exact congrArg (fun x : ℂ => L + x) (add_assoc R (-L) H).symm
      _ = L + (R - L + H) := by
        exact congrArg (fun x : ℂ => L + (x + H)) (sub_eq_add_neg R L).symm
      _ = L + C := by
        exact congrArg (fun x : ℂ => L + x) hC.symm
      _ = C + L := by
        exact add_comm L C
  have hright : R = C + L - H := by
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  calc
    R = C + L - H := by
      exact hright
    _ = (C + L) + -H := by
      exact sub_eq_add_neg (C + L) H
    _ = (L + C) + -H := by
      exact congrArg (fun x : ℂ => x + -H) (add_comm C L)
    _ = L + (C + -H) := by
      exact add_assoc L C (-H)
    _ = L + (-H + C) := by
      exact congrArg (fun x : ℂ => L + x) (add_comm C (-H))
    _ = (L + -H) + C := by
      exact (add_assoc L (-H) C).symm
    _ = L - H + C := by
      exact congrArg (fun x : ℂ => x + C) (sub_eq_add_neg L H).symm

/-- The right vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  have hpos : 0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    Eq.symm hre ▸ F.c_pos
  exact fun hzero =>
    have hre_zero : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    (ne_of_gt hpos) hre_zero

/-- The right vertical side lies strictly to the right of the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re := by
  have hre :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re =
        (F.rectangle T).c :=
    zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) t
  exact Eq.symm hre ▸ F.c_gt_one

/-- The right vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 ≠ 0 := by
  have hgt :
      1 < (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re :=
    zetaCompletedExplicitFormulaCorrectionRightPath_re_gt_one F T t
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaRightPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_gt hgt) hre_one

/-- The left vertical side never meets the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t ≠ 0 := by
  exact fun hzero =>
    have hre :
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
          1 - F.c :=
      zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
    have hre_zero : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 0 :=
      congrArg Complex.re hzero
    have hsub_zero : 1 - F.c = 0 :=
      hre.symm.trans hre_zero
    have hc_one : F.c = 1 :=
      (sub_eq_zero.mp hsub_zero).symm
    F.c_ne_one hc_one

/-- The left vertical side lies strictly to the left of the pole at `0`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hleft : 1 - F.c < 0 :=
    F.one_sub_c_neg
  exact Eq.symm hre ▸ hleft

/-- On the left vertical face, the absolute real coordinate is the fixed
distance from the `s = 0` pole to the line. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    |(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re| =
      F.c - 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hre : z.re = 1 - F.c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hneg : z.re < 0 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_re_lt_zero F T t
  have habs : |z.re| = -z.re :=
    abs_of_neg hneg
  have hneg_re : -z.re = F.c - 1 := by
    calc
      -z.re = -(1 - F.c) := by
        exact congrArg Neg.neg hre
      _ = F.c - 1 := by
        exact neg_sub 1 F.c
  exact Eq.trans habs hneg_re

/-- The left vertical face stays at least `F.c - 1` away from the `s = 0`
correction pole in norm. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    F.c - 1 ≤ ‖zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖ := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have habs_re :
      |z.re| = F.c - 1 :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_abs_re_eq_c_sub_one F T t
  have hle_abs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hle_abs_target : F.c - 1 ≤ Complex.abs z :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ Complex.abs z)
      habs_re
      hle_abs
  have habs_norm : Complex.abs z = ‖z‖ :=
    (Complex.norm_eq_abs z).symm
  exact Eq.subst
    (motive := fun x : ℝ => F.c - 1 ≤ x)
    habs_norm
    hle_abs_target

/-- The isolated `s = 0` correction coefficient is uniformly bounded on the
left vertical face by the reciprocal of the line's distance from the pole. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t‖
      ≤ 1 / (F.c - 1) := by
  let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  have hpos : 0 < F.c - 1 :=
    sub_pos.mpr F.c_gt_one
  have hle_norm : F.c - 1 ≤ ‖z‖ :=
    zetaCompletedExplicitFormulaCorrectionLeftPath_c_sub_one_le_norm F T t
  have hrecip : 1 / ‖z‖ ≤ 1 / (F.c - 1) :=
    one_div_le_one_div_of_le hpos hle_norm
  have hneg_div : -1 / z = -(1 / z) :=
    (neg_div z (1 : ℂ)).symm
  have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
    norm_neg (1 / z)
  have hnorm_div : ‖(1 : ℂ) / z‖ = ‖(1 : ℂ)‖ / ‖z‖ :=
    norm_div (1 : ℂ) z
  have hnorm_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have hcoeff :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖-(1 / z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hneg_div
      _ = ‖1 / z‖ := by
        exact hnorm_neg
      _ = ‖(1 : ℂ) / z‖ := by
        rfl
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact hnorm_div
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) hnorm_one
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1 / (F.c - 1))
    hcoeff.symm
    hrecip

/-- The shifted left vertical face lies in the fixed real strip used for the
completed transform estimates. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    min F.c (1 - F.c) - 1 / 2
        ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
        ≤ max F.c (1 - F.c) - 1 / 2 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
        (1 - F.c) - 1 / 2 := by
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re -
            (1 / 2 : ℂ).re := by
        exact Complex.sub_re
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = (1 - F.c) - (1 / 2 : ℂ).re := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).re)
          (zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t)
      _ = (1 - F.c) - 1 / 2 := by
        exact congrArg (fun x : ℝ => (1 - F.c) - x) Complex.ofReal_re
  constructor
  · have hmin : min F.c (1 - F.c) ≤ 1 - F.c :=
      min_le_right F.c (1 - F.c)
    have hsub : min F.c (1 - F.c) - 1 / 2 ≤ (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmin (1 / 2)
    exact Eq.symm hre ▸ hsub
  · have hmax : 1 - F.c ≤ max F.c (1 - F.c) :=
      le_max_right F.c (1 - F.c)
    have hsub : (1 - F.c) - 1 / 2 ≤ max F.c (1 - F.c) - 1 / 2 :=
      sub_le_sub_right hmax (1 / 2)
    exact Eq.symm hre ▸ hsub

/-- The shifted left vertical face has imaginary coordinate norm `‖t‖`. -/
theorem zetaCompletedExplicitFormulaLeftPath_shift_im_norm
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    ‖(zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im‖ =
      ‖t‖ := by
  have him :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im = t := by
    calc
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).im =
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).im -
            (1 / 2 : ℂ).im := by
        exact Complex.sub_im
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)
          (1 / 2 : ℂ)
      _ = t - (1 / 2 : ℂ).im := by
        exact congrArg
          (fun x : ℝ => x - (1 / 2 : ℂ).im)
          (zetaCompletedExplicitFormulaLeftPath_im (F.rectangle T) t)
      _ = t - 0 := by
        exact congrArg (fun x : ℝ => t - x) Complex.ofReal_im
      _ = t := by
        exact sub_zero t
  exact congrArg (fun x : ℝ => ‖x‖) him

/-- Pointwise decay for the left-face isolated `s = 0` correction integrand.

This is the genuine denominator-separation part of the all-height Cauchy
estimate; the remaining finite-window theorem must convert this vertical-line
oscillatory decay into the rectangle cancellation bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_norm_le_phiDecay
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T t : ℝ) (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
      ≤
        (1 / (F.c - 1)) *
          (hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ))) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
  have ha :
      ‖a‖ ≤ 1 / (F.c - 1) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
  have hb :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖t‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t))
  have hA_nonneg : 0 ≤ 1 / (F.c - 1) :=
    le_of_lt (div_pos zero_lt_one (sub_pos.mpr F.c_gt_one))
  have hproduct :
      ‖a * b‖
        ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤
          (1 / (F.c - 1)) *
            (hPhi.verticalStripRapidDecayConstant
              (min F.c (1 - F.c) - 1 / 2)
              (max F.c (1 - F.c) - 1 / 2) N *
            (1 + ‖t‖) ^ (-(N : ℤ))) := by
        exact mul_le_mul ha hb (norm_nonneg b) hA_nonneg
  exact hproduct

/-- IBP-backed uniform rapid decay for the left-face isolated `s = 0`
correction integrand.

The denominator is separated from the pole by the fixed distance `F.c - 1`;
the transform decay comes from the Paley-Wiener vertical integration-by-parts
owner theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_uniformRapidDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ T t : ℝ,
        ‖(-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)‖
          ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
  match
    zetaPhi_verticalStripRapidDecay_of_admissible_owner
      f
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2)
      N with
  | ⟨Cφ, hCφpos, hCφ⟩ =>
      let K : ℝ := 1 / (F.c - 1)
      have hKpos : 0 < K :=
        div_pos zero_lt_one (sub_pos.mpr F.c_gt_one)
      refine ⟨K * Cφ, mul_pos hKpos hCφpos, ?_⟩
      intro T t
      let z : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2
      let a : ℂ := -1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
      let b : ℂ := zetaCompletedExplicitFormulaPhi f z
      have hcoeff : ‖a‖ ≤ K :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleCoefficient_norm_le F T t
      have hstrip :
          min F.c (1 - F.c) - 1 / 2 ≤ z.re ∧
            z.re ≤ max F.c (1 - F.c) - 1 / 2 :=
        zetaCompletedExplicitFormulaLeftPath_shift_re_mem_strip_bounds F T t
      have hphi_raw :
          ‖b‖ ≤ Cφ * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
        hCφ z hstrip.1 hstrip.2
      have him_norm :
          ‖z.im‖ = ‖t‖ :=
        zetaCompletedExplicitFormulaLeftPath_shift_im_norm F T t
      have hphi :
          ‖b‖ ≤ Cφ * (1 + ‖t‖) ^ (-(N : ℤ)) :=
        Eq.subst
          (motive := fun u : ℝ => ‖b‖ ≤ Cφ * (1 + u) ^ (-(N : ℤ)))
          him_norm
          hphi_raw
      have hK_nonneg : 0 ≤ K :=
        le_of_lt hKpos
      have hprod :
          ‖a * b‖ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
        calc
          ‖a * b‖ = ‖a‖ * ‖b‖ := by
            exact norm_mul a b
          _ ≤ K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) := by
            exact mul_le_mul hcoeff hphi (norm_nonneg b) hK_nonneg
      have hassoc :
          K * (Cφ * (1 + ‖t‖) ^ (-(N : ℤ))) =
            (K * Cφ) * (1 + ‖t‖) ^ (-(N : ℤ)) :=
        (mul_assoc K Cφ ((1 + ‖t‖) ^ (-(N : ℤ)))).symm
      exact le_trans hprod (le_of_eq hassoc)

/-- The left vertical side never meets the pole at `1`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero
    (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 ≠ 0 := by
  have hre :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re =
        1 - (F.rectangle T).c :=
    zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) t
  have hlt : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re < 1 := by
    have hpos : 0 < (F.rectangle T).c :=
      F.c_pos
    exact Eq.symm hre ▸ sub_lt_self (1 : ℝ) hpos
  exact fun hzero =>
    have hone : zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t = 1 :=
      sub_eq_zero.mp hzero
    have hre_one : (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t).re = 1 :=
      congrArg Complex.re hone
    (ne_of_lt hlt) hre_one

/-- The shifted completed transform is continuous along the right vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- The shifted completed transform is continuous along the left vertical side. -/
theorem zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    Continuous
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
  have hPhi :
      Continuous (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) :=
    continuous_iff_continuousAt.2
      (fun z =>
        (zetaCompletedExplicitFormulaPhi_shift_differentiableAt
          hPhi z).continuousAt)
  have hpath :
      Continuous (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact hPhi.comp hpath

/-- Right vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaRightPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inl ⟨t, ht, rfl⟩
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Left vertical archimedean-channel integrability on a finite height interval,
with regularity supplied by the contour boundary-avoidance certificate. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaArchimedeanLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      ContinuousOn
        (fun t : ℝ =>
          explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
        (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
    intro t ht
    let s : ℂ := zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t
    have hpath :
        ContinuousAt
          (fun x : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x)
          t := by
      exact
        (continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)).continuousAt
    have hboundary :
        s ∈ explicitFormulaContourFamilyBoundary F T := by
      exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
    have hs0 : s ≠ 0 :=
      explicitFormulaContourSingularPoint.ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hs1 : s ≠ 1 :=
      explicitFormulaContourSingularPoint.ne_one_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΛ : completedRiemannZeta s ≠ 0 :=
      explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have hΓ : Gammaℝ s ≠ 0 :=
      explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (fun hsingular => havoid s hsingular hboundary)
    have harch :
        ContinuousAt
          (fun x : ℝ =>
            explicitFormulaArchimedeanLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x))
          t :=
      (explicitFormulaArchimedeanLogDerivative_continuousAt_of_regular
        s hs0 hs1 hΛ hΓ).comp t hpath
    have hphi :
        ContinuousAt
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) x - 1 / 2))
          t :=
      (zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous
        f hPhi F T).continuousAt
    exact (harch.mul hphi).continuousWithinAt
  exact hcont.integrableOn_compact isCompact_Icc

/-- Right vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionRightPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaRightPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_rightPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

/-- Left vertical correction-channel integrability for the original correction
log-derivative integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftVerticalIntegrableOn
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
      (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T) := by
  have hcont :
      Continuous
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) := by
    have hpath :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
    have hden0 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      hpath
    have hden1 :
        Continuous
          (fun t : ℝ => zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1) :=
      hpath.sub continuous_const
    have hfirst :
        Continuous
          (fun t : ℝ => -(1 : ℂ) /
            zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) :=
      continuous_const.div hden0
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_ne_zero F T t)
    have hsecond :
        Continuous
          (fun t : ℝ => (1 : ℂ) /
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1)) :=
      continuous_const.div hden1
        (fun t => zetaCompletedExplicitFormulaCorrectionLeftPath_sub_one_ne_zero F T t)
    have hcoeff :
        Continuous
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t)) := by
      change Continuous
        (fun t : ℝ =>
          -(1 : ℂ) / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t -
            (1 : ℂ) /
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1))
      exact hfirst.sub hsecond
    have hphi :
        Continuous
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)) :=
      zetaCompletedExplicitFormulaPhi_leftPath_shift_continuous f hPhi F T
    exact hcoeff.mul hphi
  exact hcont.integrableOn_Icc

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
      rfl

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
