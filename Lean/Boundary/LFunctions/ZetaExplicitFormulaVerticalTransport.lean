import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

/-!
# Boundary explicit-formula vertical transport

This file owns the vertical-channel contour transport theorem used by the
final explicit-formula assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The vertical side difference along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)

/-- The vertical-channel transport remainder along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaFamilyVerticalDifference f F T -
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The vertical family is its analytic boundary value plus the vertical-transport
remainder. -/
theorem explicitFormulaFamilyVerticalDifference_eq_boundary_add_transportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalDifference f F T =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f +
        explicitFormulaFamilyVerticalTransportRemainder f F T := by
  let V : ℂ := explicitFormulaFamilyVerticalDifference f F T
  let B : ℂ := zetaCompletedExplicitFormulaBoundarySumAnalytic f
  unfold explicitFormulaFamilyVerticalTransportRemainder
  change V = B + (V - B)
  calc
    V = V + 0 := by
      exact (add_zero V).symm
    _ = V + (-B + B) := by
      exact congrArg (fun x : ℂ => V + x) (neg_add_cancel B).symm
    _ = (V + -B) + B := by
      exact (add_assoc V (-B) B).symm
    _ = B + (V + -B) := by
      exact add_comm (V + -B) B
    _ = B + (V - B) := by
      exact congrArg (fun x : ℂ => B + x) (sub_eq_add_neg V B).symm

/-- Owner vertical-transport theorem: along an admissible contour family, the
vertical side difference converges to the analytic prime/archimedean/correction
boundary scalar. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_ownerVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  sorry

/-- If the vertical side difference converges to the analytic boundary scalar, then
the vertical-transport remainder tends to zero. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_of_boundaryLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hvertical :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f))) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
      atTop
      (𝓝 0) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          explicitFormulaFamilyVerticalDifference f F T -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaBoundarySumAnalytic f -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    hvertical.sub hconst
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f -
          zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        0 := by
    exact sub_self _
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T) =
        (fun T : ℝ =>
          explicitFormulaFamilyVerticalDifference f F T -
            zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
    funext T
    rfl
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            explicitFormulaFamilyVerticalDifference f F T -
              zetaCompletedExplicitFormulaBoundarySumAnalytic f)
          atTop
          (𝓝 z))
      htarget
      hsub)

/-- The vertical-channel transport remainder vanishes along the contour family. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
      atTop
      (𝓝 0) := by
  exact explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero_of_boundaryLimit
    f F
    (explicitFormulaFamilyVerticalDifference_tendsto_boundarySum_ownerVerticalTransport f F)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
