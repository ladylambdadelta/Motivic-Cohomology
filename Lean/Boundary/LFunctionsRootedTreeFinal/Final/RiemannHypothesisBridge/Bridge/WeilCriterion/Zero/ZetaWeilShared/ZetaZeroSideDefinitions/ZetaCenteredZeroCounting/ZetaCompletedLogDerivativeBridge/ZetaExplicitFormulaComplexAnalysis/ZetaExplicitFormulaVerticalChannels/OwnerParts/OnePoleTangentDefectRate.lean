import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OrientationAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities

/-!
# One-pole tangent-defect rate transport

This file owns the rate-level algebra for the isolated `s = 1` tangent
defect.  It deliberately does not prove the analytic rates for the left face
or tangent boundary; it proves the reusable transport step from those two
rates to the genuine tangent Cauchy defect.
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

/-- If two one-pole quantities converge to compatible residue values with the
same inverse-quadratic rate, then their tangent defect has that rate. -/
theorem explicitFormulaOnePole_tangentDefect_eventual_inverseQuadratic_of_component_rates
    (left tangent : ℝ → ℂ) (A B : ℂ) (ML MB : ℝ) (height : ℝ → ℝ)
    (hcancel : A - B * Complex.I = 0)
    (hleft :
      ∀ᶠ u in atTop,
        ‖left u - A‖ ≤ ML * (1 + ‖height u‖) ^ (-(2 : ℤ)))
    (htangent :
      ∀ᶠ u in atTop,
        ‖tangent u - B‖ ≤ MB * (1 + ‖height u‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖left u - tangent u * Complex.I‖
        ≤ (ML + MB) * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  exact (hleft.and htangent).mono
    (fun u hu =>
      let q : ℝ := (1 + ‖height u‖) ^ (-(2 : ℤ))
      let L : ℂ := left u
      let T : ℂ := tangent u
      have hdecomp :
          L - T * Complex.I = (L - A) - (T - B) * Complex.I := by
        exact
          explicitFormula_tangentDefect_eq_componentErrors_of_residue_cancel
            L T A B hcancel
      have hnorm :
          ‖L - T * Complex.I‖ ≤ ‖L - A‖ + ‖(T - B) * Complex.I‖ := by
        exact
          Eq.subst
            (motive := fun z : ℂ =>
              ‖z‖ ≤ ‖L - A‖ + ‖(T - B) * Complex.I‖)
            hdecomp.symm
            (norm_sub_le (L - A) ((T - B) * Complex.I))
      have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
        Complex.norm_I
      have hmul_norm : ‖(T - B) * Complex.I‖ = ‖T - B‖ := by
        calc
          ‖(T - B) * Complex.I‖ = ‖T - B‖ * ‖Complex.I‖ := by
            exact norm_mul (T - B) Complex.I
          _ = ‖T - B‖ * 1 := by
            exact congrArg (fun x : ℝ => ‖T - B‖ * x) hI_norm
          _ = ‖T - B‖ := by
            exact mul_one ‖T - B‖
      have hsum :
          ‖L - A‖ + ‖(T - B) * Complex.I‖ ≤ ML * q + MB * q := by
        have hT :
            ‖(T - B) * Complex.I‖ ≤ MB * q :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ MB * q)
            hmul_norm.symm
            hu.2
        exact add_le_add hu.1 hT
      have hfactor :
          ML * q + MB * q = (ML + MB) * q :=
        (add_mul ML MB q).symm
      by
        exact hnorm.trans (hsum.trans_eq hfactor))

/-- Rate transport for the actual scheduled one-pole tangent defect. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_eventual_inverseQuadratic_of_component_rates
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ) (ML MB : ℝ)
    (hcancel : A - B * Complex.I = 0)
    (hleft :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) - A‖
          ≤ ML *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ MB *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I‖
        ≤ (ML + MB) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    explicitFormulaOnePole_tangentDefect_eventual_inverseQuadratic_of_component_rates
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      A
      B
      ML
      MB
      (fun u : ℝ => (F.rectangle (h.height_schedule.height u)).T)
      hcancel
      hleft
      htangent

/-- Generic rate transport for a tangent boundary that differs from the
standard boundary by two copies of a horizontal orientation remainder. -/
theorem explicitFormula_tangentBoundary_eventual_inverseQuadratic_of_standard_and_horizontal
    (standard tangent horizontal : ℝ → ℂ) (B : ℂ) (MS MH : ℝ) (height : ℝ → ℝ)
    (hpoint :
      ∀ u : ℝ, tangent u = standard u + (horizontal u + horizontal u))
    (hstandard :
      ∀ᶠ u in atTop,
        ‖standard u - B‖ ≤ MS * (1 + ‖height u‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ᶠ u in atTop,
        ‖horizontal u‖ ≤ MH * (1 + ‖height u‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖tangent u - B‖
        ≤ (MS + (MH + MH)) * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  exact (hstandard.and hhorizontal).mono
    (fun u hu =>
      let q : ℝ := (1 + ‖height u‖) ^ (-(2 : ℤ))
      let S : ℂ := standard u
      let T : ℂ := tangent u
      let H : ℂ := horizontal u
      have hdecomp : T - B = (S - B) + (H + H) := by
        calc
          T - B = S + (H + H) - B := by
            exact congrArg (fun z : ℂ => z - B) (hpoint u)
          _ = (S + (H + H)) + -B := by
            exact sub_eq_add_neg (S + (H + H)) B
          _ = S + ((H + H) + -B) := by
            exact add_assoc S (H + H) (-B)
          _ = S + (-B + (H + H)) := by
            exact congrArg (fun z : ℂ => S + z) (add_comm (H + H) (-B))
          _ = (S + -B) + (H + H) := by
            exact (add_assoc S (-B) (H + H)).symm
          _ = (S - B) + (H + H) := by
            exact congrArg (fun z : ℂ => z + (H + H)) (sub_eq_add_neg S B).symm
      have hnorm :
          ‖T - B‖ ≤ ‖S - B‖ + ‖H + H‖ := by
        exact
          Eq.subst
            (motive := fun z : ℂ => ‖z‖ ≤ ‖S - B‖ + ‖H + H‖)
            hdecomp.symm
            (norm_add_le (S - B) (H + H))
      have hHH : ‖H + H‖ ≤ MH * q + MH * q := by
        exact (norm_add_le H H).trans (add_le_add hu.2 hu.2)
      have hsum :
          ‖S - B‖ + ‖H + H‖ ≤ MS * q + (MH * q + MH * q) :=
        add_le_add hu.1 hHH
      have hfactor_inner :
          MH * q + MH * q = (MH + MH) * q :=
        (add_mul MH MH q).symm
      have hfactor :
          MS * q + (MH * q + MH * q) =
            (MS + (MH + MH)) * q := by
        calc
          MS * q + (MH * q + MH * q) =
              MS * q + (MH + MH) * q := by
            exact congrArg (fun z : ℝ => MS * q + z) hfactor_inner
          _ = (MS + (MH + MH)) * q := by
            exact (add_mul MS (MH + MH) q).symm
      by
        exact hnorm.trans (hsum.trans_eq hfactor))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
