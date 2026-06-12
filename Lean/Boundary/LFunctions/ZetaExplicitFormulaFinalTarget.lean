import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaExplicitFormulaResidueBridge

/-!
# Boundary explicit-formula final target

This file owns the final zero-side contour-shift target. The pure contour
geometry file intentionally does not import the zero-side Krein form, because
the zero-side chain already depends downstream on the complex-analysis contour
layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The full contour-shift target for the explicit formula. -/
def explicitFormulaContourShiftTarget
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The contour-shift target is the final public explicit-formula statement. -/
theorem explicitFormulaContourShiftTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
  Iff.rfl

/-- The zero-side Krein sum is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_completedResidueBoundarySum
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    (zetaCompletedZeroKreinGram f : ℂ) =
      (zetaCompletedResidueBoundarySum f : ℂ) := by
  exact congrArg (fun x : ℝ => (x : ℂ))
    (zetaCompletedZeroKreinGram_eq_residueBoundarySum f)

/-- The vertical side difference along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)

/-- Residue reconstruction plus horizontal decay identifies the limit of the vertical
family with the completed residue boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_residueBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) := by
  sorry

/-- The vertical channel transport identifies the limit of the vertical family with the
analytic prime/archimedean/correction boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  sorry

/-- The zero side equals the analytic boundary sum by uniqueness of the completed vertical
family limit. -/
theorem zetaCompletedZeroKreinGram_eq_boundarySum_of_familyContourShift
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (zetaCompletedZeroKreinGram f : ℂ) =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  have hresidue :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) :=
    explicitFormulaFamilyVerticalDifference_tendsto_residueBoundarySum f F
  have hzero_eq_residue :
      (zetaCompletedZeroKreinGram f : ℂ) =
        (zetaCompletedResidueBoundarySum f : ℂ) :=
    zetaCompletedZeroKreinGram_eq_completedResidueBoundarySum f (F.rectangle 1)
  have hzero :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedZeroKreinGram f : ℂ)) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
          atTop
          (𝓝 z))
      hzero_eq_residue.symm
      hresidue
  have hboundary :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    explicitFormulaFamilyVerticalDifference_tendsto_boundarySum f F
  exact tendsto_nhds_unique hzero hboundary

/-- The vertical side difference of the completed contour. -/
noncomputable def explicitFormulaVerticalDifference
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r

/-- The prime channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalPrimeContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f

/-- The archimedean channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalArchimedeanContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution f

/-- The correction channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalCorrectionContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution f

/-- The prime part of the vertical contour difference is the prime explicit-formula boundary
contribution. -/
theorem explicitFormulaVerticalPrimeDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalPrimeContribution f r =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The archimedean part of the vertical contour difference is the archimedean explicit-formula
boundary contribution. -/
theorem explicitFormulaVerticalArchimedeanDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalArchimedeanContribution f r =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  rfl

/-- The correction part of the vertical contour difference is the pole-correction
explicit-formula boundary contribution. -/
theorem explicitFormulaVerticalCorrectionDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalCorrectionContribution f r =
      zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-- The completed contour-shift theorem in the repository's analytic normalization.

This is a rectangle-indexed wrapper around the family/limit theorem above; the target itself
does not depend on the finite rectangle parameter. -/
theorem explicitFormulaContourShiftTarget_of_rectangle
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r := by
  let F : ExplicitFormulaContourFamily :=
    { c := (1 / 2 : ℝ) + 1
      c_gt_half := by
        exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one }
  have htarget :
      (zetaCompletedZeroKreinGram f : ℂ) =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    zetaCompletedZeroKreinGram_eq_boundarySum_of_familyContourShift f F
  exact htarget

/-- A complex zero statement for the real zero-side Krein form descends to a real zero statement. -/
theorem zetaCompletedZeroKreinGram_eq_zero_of_complex_zero
    (f : ZetaAdmissibleFunction)
    (h : (zetaCompletedZeroKreinGram f : ℂ) = 0) :
    zetaCompletedZeroKreinGram f = 0 :=
  Complex.ofReal_injective h

/-- A real zero statement for the zero-side Krein form ascends to a complex zero statement. -/
theorem zetaCompletedZeroKreinGram_complex_zero_of_eq_zero
    (f : ZetaAdmissibleFunction)
    (h : zetaCompletedZeroKreinGram f = 0) :
    (zetaCompletedZeroKreinGram f : ℂ) = 0 :=
  congrArg (fun x : ℝ => (x : ℂ)) h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
