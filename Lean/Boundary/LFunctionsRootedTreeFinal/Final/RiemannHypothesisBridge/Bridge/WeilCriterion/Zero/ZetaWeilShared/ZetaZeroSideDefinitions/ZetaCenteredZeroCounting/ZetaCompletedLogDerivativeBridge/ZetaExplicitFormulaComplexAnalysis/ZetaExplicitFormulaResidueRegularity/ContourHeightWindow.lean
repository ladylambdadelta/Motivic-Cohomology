import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.Owner

/-!
# Completed-zero contour height window

The contour window uses the raw open vertical strip `|Im rho| < T`. It is distinct from
the weighted counting window `1 + |Im rho| <= T`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The uncentered residue point and the weighted centered-height coordinate have the
same imaginary coordinate. -/
theorem completedZeroResidueCoordinate_im_eq_centeredZero_im
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    (completedZeroResidueCoordinate rho).im =
      (zetaCenteredZero (rho : ℂ)).im := by
  calc
    (completedZeroResidueCoordinate rho).im =
        ((1 / 2 : ℂ) + (rho : ℂ)).im := by
      rfl
    _ = (rho : ℂ).im := by
      exact Eq.trans
        (Complex.add_im (1 / 2 : ℂ) (rho : ℂ))
        (zero_add (rho : ℂ).im)
    _ = ((rho : ℂ) - (1 / 2 : ℂ)).im := by
      exact (Eq.trans
        (Complex.sub_im (rho : ℂ) (1 / 2 : ℂ))
        (sub_zero (rho : ℂ).im)).symm
    _ = (zetaCenteredZero (rho : ℂ)).im := by
      rfl

/-- The finite completed-zero window cut out by the open vertical contour strip. -/
noncomputable def explicitFormulaCompletedZeroContourHeightWindow
    (T : ℝ) : Finset {rho : ℂ // ZetaCompletedZero rho} :=
  (explicitFormulaCompletedZeroHeightWindow (T + 1)).filter
    (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
      |(completedZeroResidueCoordinate rho).im| < T)

/-- Membership in the contour-height window is exactly raw imaginary-height membership. -/
theorem mem_explicitFormulaCompletedZeroContourHeightWindow_iff
    (T : ℝ) (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
      |(completedZeroResidueCoordinate rho).im| < T := by
  apply Iff.intro
  · intro hrho
    exact (Finset.mem_filter.mp hrho).2
  · intro him
    have hnormResidue :
        ‖(completedZeroResidueCoordinate rho).im‖ < T :=
      Eq.subst
        (motive := fun value : ℝ => value < T)
        (Real.norm_eq_abs (completedZeroResidueCoordinate rho).im).symm
        him
    have hnormCentered :
        ‖(zetaCenteredZero (rho : ℂ)).im‖ < T :=
      Eq.subst
        (motive := fun value : ℝ => ‖value‖ < T)
        (completedZeroResidueCoordinate_im_eq_centeredZero_im rho)
        hnormResidue
    have hheight : zetaCompletedZeroCenteredHeight rho ≤ T + 1 :=
      le_of_lt (add_lt_add_left hnormCentered 1)
    have hweighted : rho ∈ explicitFormulaCompletedZeroHeightWindow (T + 1) :=
      (mem_explicitFormulaCompletedZeroHeightWindow_iff (T + 1) rho).mpr hheight
    exact Finset.mem_filter.mpr (And.intro hweighted him)

/-- Contour-height windows are monotone in their raw vertical cutoff. -/
theorem explicitFormulaCompletedZeroContourHeightWindow_mono
    {S T : ℝ} (hST : S ≤ T) :
    explicitFormulaCompletedZeroContourHeightWindow S ⊆
      explicitFormulaCompletedZeroContourHeightWindow T := by
  intro rho hrho
  have hraw : |(completedZeroResidueCoordinate rho).im| < S :=
    (mem_explicitFormulaCompletedZeroContourHeightWindow_iff S rho).mp hrho
  exact (mem_explicitFormulaCompletedZeroContourHeightWindow_iff T rho).mpr
    (lt_of_lt_of_le hraw hST)

/-- The raw contour-height windows exhaust the completed-zero subtype. -/
theorem explicitFormulaCompletedZeroContourHeightWindow_tendsto_atTop :
    Tendsto explicitFormulaCompletedZeroContourHeightWindow atTop atTop := by
  exact Monotone.tendsto_atTop_finset
    (fun S T hST => explicitFormulaCompletedZeroContourHeightWindow_mono hST)
    (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
      Exists.intro
        (|(completedZeroResidueCoordinate rho).im| + 1)
        ((mem_explicitFormulaCompletedZeroContourHeightWindow_iff
          (|(completedZeroResidueCoordinate rho).im| + 1) rho).mpr
          (lt_add_of_pos_right
            |(completedZeroResidueCoordinate rho).im| zero_lt_one)))

/-- The finite residue sum over the exact raw contour-height window. -/
noncomputable def explicitFormulaCompletedZeroContourHeightWindowResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  ∑ rho in explicitFormulaCompletedZeroContourHeightWindow T,
    explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero rho)

/-- The finite zero-side sum over the exact raw contour-height window. -/
noncomputable def explicitFormulaCompletedZeroContourHeightWindowZeroSideSum
    (f : ZetaAdmissibleFunction) (T : ℝ) : ℂ :=
  ∑ rho in explicitFormulaCompletedZeroContourHeightWindow T,
    zetaZeroSideContribution (rho : ℂ) f

/-- The raw contour-height zero-side sums converge to the completed zero-side series. -/
theorem explicitFormulaCompletedZeroContourHeightWindowZeroSideSum_tendsto_tsum
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T)
      atTop
      (𝓝
        (∑' rho : {rho : ℂ // ZetaCompletedZero rho},
          zetaZeroSideContribution (rho : ℂ) f)) := by
  have hwindow :
      Tendsto
        (fun T : ℝ =>
          ∑ rho in explicitFormulaCompletedZeroContourHeightWindow T,
            zetaZeroSideContribution (rho : ℂ) f)
        atTop
        (𝓝
          (∑' rho : {rho : ℂ // ZetaCompletedZero rho},
            zetaZeroSideContribution (rho : ℂ) f)) :=
    hsum.hasSum.comp explicitFormulaCompletedZeroContourHeightWindow_tendsto_atTop
  have hpointwise :
      (fun T : ℝ => explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T) =
        (fun T : ℝ =>
          ∑ rho in explicitFormulaCompletedZeroContourHeightWindow T,
            zetaZeroSideContribution (rho : ℂ) f) := by
    exact funext
      (fun T : ℝ => Eq.refl
        (explicitFormulaCompletedZeroContourHeightWindowZeroSideSum f T))
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      Tendsto function atTop
        (𝓝
          (∑' rho : {rho : ℂ // ZetaCompletedZero rho},
            zetaZeroSideContribution (rho : ℂ) f)))
    hpointwise.symm
    hwindow

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
