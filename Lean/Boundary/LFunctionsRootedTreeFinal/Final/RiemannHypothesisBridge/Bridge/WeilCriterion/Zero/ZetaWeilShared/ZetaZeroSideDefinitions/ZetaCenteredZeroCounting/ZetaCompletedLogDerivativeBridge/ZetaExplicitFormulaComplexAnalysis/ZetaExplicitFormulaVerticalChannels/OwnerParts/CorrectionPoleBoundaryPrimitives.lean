import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.Core
import Mathlib.MeasureTheory.Integral.SetIntegral

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

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

/-- The isolated `s = 0` correction kernel as a function of the contour variable. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleKernel
    (f : ZetaAdmissibleFunction) (z : ℂ) : ℂ :=
  (-1 / z) * zetaCompletedExplicitFormulaPhi f (z - 1 / 2)

/-- Algebraic residue cancellation for the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
    (z φ : ℂ) (hz : z ≠ 0) :
    z * ((-1 / z) * φ) = -φ := by
  have hdiv_neg :
      -1 / z = -(1 / z) :=
    neg_div z (1 : ℂ)
  have hcoeff :
      z * (-1 / z) = -1 := by
    calc
      z * (-1 / z) =
          z * (-(1 / z)) := by
        exact congrArg (fun a : ℂ => z * a) hdiv_neg
      _ = -(z * (1 / z)) := by
        exact mul_neg z (1 / z)
      _ = -(z * z⁻¹) := by
        have hone_div : 1 / z = z⁻¹ := by
          exact one_div z
        exact congrArg (fun a : ℂ => -(z * a)) hone_div
      _ = -1 := by
        exact congrArg Neg.neg (mul_inv_cancel₀ hz)
  calc
    z * ((-1 / z) * φ) =
        (z * (-1 / z)) * φ := by
      exact (mul_assoc z (-1 / z) φ).symm
    _ = (-1) * φ := by
      exact congrArg (fun a : ℂ => a * φ) hcoeff
    _ = -φ := by
      exact neg_one_mul φ

/-- Local residue of the isolated `s = 0` correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_tendsto
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) := by
  have hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) := by
    have hcontinuous :
        ContinuousAt
          (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (0 : ℂ) :=
      (zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi (0 : ℂ)).continuousAt
    exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have htarget_arg : (0 : ℂ) - 1 / 2 = -(1 / 2 : ℂ) := by
    exact zero_sub (1 / 2 : ℂ)
  have hneg :
      Tendsto
        (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hphi.neg
  have hpointwise :
      (fun z : ℂ =>
        z *
          ((-1 / z) *
            zetaCompletedExplicitFormulaPhi f (z - 1 / 2))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => -zetaCompletedExplicitFormulaPhi f (z - 1 / 2)) := by
    exact
      eventually_nhdsWithin_of_forall
        (fun z hz_ne =>
          zetaCompletedExplicitFormulaCorrectionZeroPole_localResidue_algebra
            z
            (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
            hz_ne)
  have hraw :
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    Tendsto.congr' hpointwise.symm hneg
  exact Eq.subst
    (motive := fun w : ℂ =>
      Tendsto
        (fun z : ℂ =>
          z *
            ((-1 / z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2)))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (-zetaCompletedExplicitFormulaPhi f w)))
    htarget_arg
    hraw

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
    integral_smul_const
      (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
      Complex.I
  have hL : LT = L * Complex.I :=
    integral_smul_const
      (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
      Complex.I
  have hU : TT = U := rfl
  have hB : BT = B := rfl
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
    integral_smul_const
      (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t))
      Complex.I
  have hL : LT = L * Complex.I :=
    integral_smul_const
      (μ := volume.restrict (Set.Icc (-(F.rectangle T).T) (F.rectangle T).T))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t))
      Complex.I
  have hU : TT = U := rfl
  have hB : BT = B := rfl
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

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
