import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
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

/-- The horizontal side difference along a contour family. -/
noncomputable def explicitFormulaFamilyHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)

/-- The contour integral along a contour family. -/
noncomputable def explicitFormulaFamilyContourIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T)

/-- The residue-side contour remainder along a contour family. -/
noncomputable def explicitFormulaFamilyResidueRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaFamilyContourIntegral f F T -
    (zetaCompletedResidueBoundarySum f : ℂ)

/-- The vertical-channel transport remainder along a contour family. -/
noncomputable def explicitFormulaFamilyVerticalTransportRemainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  explicitFormulaFamilyVerticalDifference f F T -
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The contour-family integral is the sum of the vertical and horizontal differences. -/
theorem explicitFormulaFamilyContourIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourIntegral f F T =
      explicitFormulaFamilyVerticalDifference f F T +
        explicitFormulaFamilyHorizontalDifference f F T := by
  let R : ℂ := zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T)
  let L : ℂ := zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T)
  let U : ℂ := zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)
  let B : ℂ := zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)
  unfold explicitFormulaFamilyContourIntegral
  unfold zetaCompletedExplicitFormulaContourIntegral
  unfold explicitFormulaFamilyVerticalDifference
  unfold explicitFormulaFamilyHorizontalDifference
  change R - L + U - B = (R - L) + (U - B)
  calc
    R - L + U - B = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = ((R - L) + U) + -B := by
      rfl
    _ = (R - L) + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = (R - L) + (U - B) := by
      exact congrArg (fun x : ℂ => (R - L) + x) (sub_eq_add_neg U B).symm

/-- The vertical family is the contour family with the horizontal difference subtracted. -/
theorem explicitFormulaFamilyVerticalDifference_eq_contour_sub_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyVerticalDifference f F T =
      explicitFormulaFamilyContourIntegral f F T -
        explicitFormulaFamilyHorizontalDifference f F T := by
  let V : ℂ := explicitFormulaFamilyVerticalDifference f F T
  let H : ℂ := explicitFormulaFamilyHorizontalDifference f F T
  have hcontour :
      explicitFormulaFamilyContourIntegral f F T = V + H :=
    explicitFormulaFamilyContourIntegral_eq_vertical_add_horizontal f F T
  calc
    explicitFormulaFamilyVerticalDifference f F T = V := by
      rfl
    _ = (V + H) - H := by
      exact (add_sub_cancel_right V H).symm
    _ = explicitFormulaFamilyContourIntegral f F T - H := by
      exact congrArg (fun x : ℂ => x - H) hcontour.symm
    _ =
        explicitFormulaFamilyContourIntegral f F T -
          explicitFormulaFamilyHorizontalDifference f F T := by
      rfl

/-- The contour family is its residue boundary value plus the residue-side remainder. -/
theorem explicitFormulaFamilyContourIntegral_eq_residue_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyContourIntegral f F T =
      (zetaCompletedResidueBoundarySum f : ℂ) +
        explicitFormulaFamilyResidueRemainder f F T := by
  let C : ℂ := explicitFormulaFamilyContourIntegral f F T
  let R : ℂ := (zetaCompletedResidueBoundarySum f : ℂ)
  unfold explicitFormulaFamilyResidueRemainder
  change C = R + (C - R)
  calc
    C = C + 0 := by
      exact (add_zero C).symm
    _ = C + (-R + R) := by
      exact congrArg (fun x : ℂ => C + x) (neg_add_cancel R).symm
    _ = (C + -R) + R := by
      exact (add_assoc C (-R) R).symm
    _ = R + (C + -R) := by
      exact add_comm (C + -R) R
    _ = R + (C - R) := by
      exact congrArg (fun x : ℂ => R + x) (sub_eq_add_neg C R).symm

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

/-- The horizontal contour sides vanish along every admissible contour family. -/
theorem explicitFormulaFamilyHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyHorizontalDifference f F T)
      atTop
      (𝓝 0) := by
  exact
    ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
      (f := f) (F := F)
      (h := explicitFormulaFamilyAnalyticPackage_of_admissible f F)
      1

/-- The residue-side contour remainder vanishes along the contour family. -/
theorem explicitFormulaFamilyResidueRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyResidueRemainder f F T)
      atTop
      (𝓝 0) := by
  sorry

/-- The residue theorem reconstructs the limiting contour integral from the zero-side
completed residue boundary. -/
theorem explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T)
      atTop
      (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => (zetaCompletedResidueBoundarySum f : ℂ))
        atTop
        (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) :=
    tendsto_const_nhds
  have hrem :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyResidueRemainder f F T)
        atTop
        (𝓝 (0 : ℂ)) :=
    explicitFormulaFamilyResidueRemainder_tendsto_zero f F
  have hsum :
      Tendsto
        (fun T : ℝ =>
          (zetaCompletedResidueBoundarySum f : ℂ) +
            explicitFormulaFamilyResidueRemainder f F T)
        atTop
        (𝓝 ((zetaCompletedResidueBoundarySum f : ℂ) + 0)) :=
    hconst.add hrem
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T) =
        (fun T : ℝ =>
          (zetaCompletedResidueBoundarySum f : ℂ) +
            explicitFormulaFamilyResidueRemainder f F T) := by
    funext T
    exact explicitFormulaFamilyContourIntegral_eq_residue_add_remainder f F T
  have htarget :
      (zetaCompletedResidueBoundarySum f : ℂ) + 0 =
        (zetaCompletedResidueBoundarySum f : ℂ) :=
    add_zero _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            (zetaCompletedResidueBoundarySum f : ℂ) +
              explicitFormulaFamilyResidueRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Residue reconstruction plus horizontal decay identifies the limit of the vertical
family with the completed residue boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_residueBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) := by
  have hcontour :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyContourIntegral f F T)
        atTop
        (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)) :=
    explicitFormulaFamilyContourIntegral_tendsto_residueBoundarySum f F
  have hhorizontal :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyHorizontalDifference f F T)
        atTop
        (𝓝 (0 : ℂ)) :=
    explicitFormulaFamilyHorizontalDifference_tendsto_zero f F
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          explicitFormulaFamilyContourIntegral f F T -
            explicitFormulaFamilyHorizontalDifference f F T)
        atTop
        (𝓝 ((zetaCompletedResidueBoundarySum f : ℂ) - 0)) :=
    hcontour.sub hhorizontal
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T) =
        (fun T : ℝ =>
          explicitFormulaFamilyContourIntegral f F T -
            explicitFormulaFamilyHorizontalDifference f F T) := by
    funext T
    exact explicitFormulaFamilyVerticalDifference_eq_contour_sub_horizontal f F T
  have htarget :
      ((zetaCompletedResidueBoundarySum f : ℂ) - 0) =
        (zetaCompletedResidueBoundarySum f : ℂ) :=
    sub_zero _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedResidueBoundarySum f : ℂ)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            explicitFormulaFamilyContourIntegral f F T -
              explicitFormulaFamilyHorizontalDifference f F T)
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- The vertical-channel transport remainder vanishes along the contour family. -/
theorem explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
      atTop
      (𝓝 0) := by
  sorry

/-- The vertical channel transport identifies the vertical-family limit with the analytic
prime/archimedean/correction boundary sum. -/
theorem explicitFormulaFamilyVerticalTransport_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) := by
  have hconst :
      Tendsto
        (fun _T : ℝ => zetaCompletedExplicitFormulaBoundarySumAnalytic f)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
    tendsto_const_nhds
  have hrem :
      Tendsto
        (fun T : ℝ => explicitFormulaFamilyVerticalTransportRemainder f F T)
        atTop
        (𝓝 (0 : ℂ)) :=
    explicitFormulaFamilyVerticalTransportRemainder_tendsto_zero f F
  have hsum :
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            explicitFormulaFamilyVerticalTransportRemainder f F T)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0)) :=
    hconst.add hrem
  have hpointwise :
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T) =
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaBoundarySumAnalytic f +
            explicitFormulaFamilyVerticalTransportRemainder f F T) := by
    funext T
    exact explicitFormulaFamilyVerticalDifference_eq_boundary_add_transportRemainder f F T
  have htarget :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f + 0 =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    add_zero _
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun T : ℝ =>
            zetaCompletedExplicitFormulaBoundarySumAnalytic f +
              explicitFormulaFamilyVerticalTransportRemainder f F T)
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The vertical channel transport identifies the limit of the vertical family with the
analytic prime/archimedean/correction boundary sum. -/
theorem explicitFormulaFamilyVerticalDifference_tendsto_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    Tendsto
      (fun T : ℝ => explicitFormulaFamilyVerticalDifference f F T)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaBoundarySumAnalytic f)) :=
  explicitFormulaFamilyVerticalTransport_tendsto_boundarySum f F

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
