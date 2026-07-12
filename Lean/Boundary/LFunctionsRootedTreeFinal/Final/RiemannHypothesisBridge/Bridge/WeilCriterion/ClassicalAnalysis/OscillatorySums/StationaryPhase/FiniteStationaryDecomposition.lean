import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.NonstationaryPhase

/-!
# Finite stationary-window assembly

This file owns the exact finite decomposition into a left nonstationary tail,
a central stationary window, and a right nonstationary tail.  It does not
estimate the central window; that estimate belongs to the stationary-phase
owner.  The assembly theorem is purely interval-additivity plus the norm
triangle inequality.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Exact three-piece interval decomposition. -/
theorem intervalIntegral_three_piece_decomposition
    (f : ℝ → ℂ)
    (left center radius right : ℝ)
    (hleft_center : left ≤ center - radius)
    (hcenter_right : center - radius ≤ center + radius)
    (hright : center + radius ≤ right)
    (hleft_integrable : IntervalIntegrable f volume left (center - radius))
    (hcentral_integrable :
      IntervalIntegrable f volume (center - radius) (center + radius))
    (hright_integrable : IntervalIntegrable f volume (center + radius) right) :
    (∫ x in left..right, f x) =
      (∫ x in left..center - radius, f x) +
        (∫ x in center - radius..center + radius, f x) +
        (∫ x in center + radius..right, f x) := by
  have hleft_central :
      (∫ x in left..center - radius, f x) +
          ∫ x in center - radius..center + radius, f x =
        ∫ x in left..center + radius, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      hleft_integrable hcentral_integrable
  have hleft_central_right :
      (∫ x in left..center + radius, f x) +
          ∫ x in center + radius..right, f x =
        ∫ x in left..right, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hleft_integrable.trans hcentral_integrable)
      hright_integrable
  have hsum :
      ((∫ x in left..center - radius, f x) +
          (∫ x in center - radius..center + radius, f x)) +
            (∫ x in center + radius..right, f x) =
        ∫ x in left..right, f x := by
    exact
      (congrArg
        (fun value : ℂ => value + ∫ x in center + radius..right, f x)
        hleft_central).trans
        hleft_central_right
  exact hsum.symm

/-- Norm assembly for a finite stationary window. -/
theorem norm_intervalIntegral_le_three_piece_bounds
    (f : ℝ → ℂ)
    (left center radius right : ℝ)
    {leftBound centralBound rightBound : ℝ}
    (hleft_center : left ≤ center - radius)
    (hcenter_right : center - radius ≤ center + radius)
    (hright : center + radius ≤ right)
    (hleft_integrable : IntervalIntegrable f volume left (center - radius))
    (hcentral_integrable :
      IntervalIntegrable f volume (center - radius) (center + radius))
    (hright_integrable : IntervalIntegrable f volume (center + radius) right)
    (hleft_bound :
      ‖∫ x in left..center - radius, f x‖ ≤ leftBound)
    (hcentral_bound :
      ‖∫ x in center - radius..center + radius, f x‖ ≤ centralBound)
    (hright_bound :
      ‖∫ x in center + radius..right, f x‖ ≤ rightBound) :
    ‖∫ x in left..right, f x‖ ≤ leftBound + centralBound + rightBound := by
  have hdecomposition :=
    intervalIntegral_three_piece_decomposition
      f left center radius right hleft_center hcenter_right hright
      hleft_integrable hcentral_integrable hright_integrable
  have htriangle_left :
      ‖(∫ x in left..center - radius, f x) +
          ∫ x in center - radius..center + radius, f x‖ ≤
        ‖∫ x in left..center - radius, f x‖ +
          ‖∫ x in center - radius..center + radius, f x‖ :=
    norm_add_le _ _
  have htriangle :
      ‖(∫ x in left..center - radius, f x) +
          (∫ x in center - radius..center + radius, f x) +
            (∫ x in center + radius..right, f x)‖ ≤
        ‖∫ x in left..center - radius, f x‖ +
          ‖∫ x in center - radius..center + radius, f x‖ +
            ‖∫ x in center + radius..right, f x‖ := by
    have hright_triangle_left :
        ‖((∫ x in left..center - radius, f x) +
            (∫ x in center - radius..center + radius, f x)) +
              (∫ x in center + radius..right, f x)‖ ≤
          ‖(∫ x in left..center - radius, f x) +
              ∫ x in center - radius..center + radius, f x‖ +
            ‖∫ x in center + radius..right, f x‖ :=
      norm_add_le
        ((∫ x in left..center - radius, f x) +
          ∫ x in center - radius..center + radius, f x)
        (∫ x in center + radius..right, f x)
    exact
      le_trans hright_triangle_left
        (add_le_add_right htriangle_left
          ‖∫ x in center + radius..right, f x‖)
  have hbound_left :
      ‖∫ x in left..center - radius, f x‖ +
          ‖∫ x in center - radius..center + radius, f x‖ +
            ‖∫ x in center + radius..right, f x‖ ≤
        leftBound + centralBound + rightBound := by
    exact
      add_le_add
        (add_le_add hleft_bound hcentral_bound)
        hright_bound
  have htriangle_left_assoc :
      ‖((∫ x in left..center - radius, f x) +
          ∫ x in center - radius..center + radius, f x) +
            ∫ x in center + radius..right, f x‖ ≤
        ‖∫ x in left..center - radius, f x‖ +
          ‖∫ x in center - radius..center + radius, f x‖ +
            ‖∫ x in center + radius..right, f x‖ := by
    exact htriangle
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤ leftBound + centralBound + rightBound)
      hdecomposition.symm
      (le_trans htriangle_left_assoc hbound_left)

end

end LFunctions
end Boundary
