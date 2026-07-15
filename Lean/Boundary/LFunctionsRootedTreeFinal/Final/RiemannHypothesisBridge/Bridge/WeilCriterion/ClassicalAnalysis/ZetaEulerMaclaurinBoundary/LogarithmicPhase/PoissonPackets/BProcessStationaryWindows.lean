import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.SharpMonotoneStationaryTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalActiveBudget

/-!
# Phase-adapted B-process stationary windows

For a logarithmic packet with stationary center `x_m`, the window radius that
balances central mass against reciprocal-derivative tails is

`x_m / sqrt (1 + ‖t‖)`.

Unlike the radius `sqrt x_m`, this radius gives a uniform packet scale
`x_m / sqrt (1 + ‖t‖)` throughout every relation between the block endpoint
and the spectral parameter.  Summing over approximately `‖t‖ / a` active
modes on a dyadic block therefore gives the required square-root scale.

This file owns the radius, window geometry, finite interior family, and its
relation to the existing active mode range.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Positive global scale used by the logarithmic B-process window. -/
def Complex.logarithmicPhaseBProcessScale
    (t : ℝ) : ℝ :=
  Real.sqrt (1 + ‖t‖)

/-- Radius balancing central length and reciprocal-derivative tails. -/
def Complex.logarithmicPhaseBProcessRadius
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseFourierStationaryPoint t m /
    Complex.logarithmicPhaseBProcessScale t

def Complex.logarithmicPhaseBProcessWindowLeft
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseFourierStationaryPoint t m -
    Complex.logarithmicPhaseBProcessRadius t m

def Complex.logarithmicPhaseBProcessWindowRight
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseFourierStationaryPoint t m +
    Complex.logarithmicPhaseBProcessRadius t m

def Complex.logarithmicPhaseBProcessWindowWidth
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseBProcessWindowRight t m -
    Complex.logarithmicPhaseBProcessWindowLeft t m

def Complex.logarithmicPhasePoissonBProcessInteriorModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonModeRange t a).filter
    (fun m : ℤ =>
      m < 0 ∧
        (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m ∧
        Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ))

theorem Complex.logarithmicPhaseBProcessScale_sq
    (t : ℝ) :
    Complex.logarithmicPhaseBProcessScale t *
        Complex.logarithmicPhaseBProcessScale t =
      1 + ‖t‖ := by
  unfold Complex.logarithmicPhaseBProcessScale
  exact Real.mul_self_sqrt (add_nonneg zero_le_one (norm_nonneg t))

theorem Complex.logarithmicPhaseBProcessScale_pos
    (t : ℝ) :
    0 < Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessScale
  exact Real.sqrt_pos.mpr
    (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg t))

theorem Complex.logarithmicPhaseBProcessScale_ne_zero
    (t : ℝ) :
    Complex.logarithmicPhaseBProcessScale t ≠ 0 :=
  ne_of_gt (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseBProcessScale_one_le
    (t : ℝ) :
    1 ≤ Complex.logarithmicPhaseBProcessScale t := by
  have hone : (1 : ℝ) ≤ 1 + ‖t‖ :=
    le_add_of_nonneg_right (norm_nonneg t)
  have hsqrt := Real.sqrt_le_sqrt hone
  have hsqrtOne : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ Complex.logarithmicPhaseBProcessScale t)
    hsqrtOne hsqrt

theorem Complex.logarithmicPhaseBProcessRadius_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 < Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessRadius
  exact div_pos
    (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm)
    (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseBProcessRadius_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessRadius t m :=
  le_of_lt (Complex.logarithmicPhaseBProcessRadius_pos t ht hm)

theorem Complex.logarithmicPhaseBProcessRadius_le_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseBProcessRadius t m ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hcenterNonneg :=
    le_of_lt (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm)
  have hscale := Complex.logarithmicPhaseBProcessScale_one_le t
  have hscaled :=
    mul_le_mul_of_nonneg_left hscale hcenterNonneg
  have hcenterScaled :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m *
          Complex.logarithmicPhaseBProcessScale t :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ Complex.logarithmicPhaseFourierStationaryPoint t m *
          Complex.logarithmicPhaseBProcessScale t)
      (mul_one _)
      hscaled
  exact (div_le_iff₀ (Complex.logarithmicPhaseBProcessScale_pos t)).mpr
    hcenterScaled

theorem Complex.logarithmicPhaseBProcessWindowLeft_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    0 ≤ Complex.logarithmicPhaseBProcessWindowLeft t m := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseBProcessRadius_le_center t ht hm)

theorem Complex.logarithmicPhaseBProcessWindowLeft_lt_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseBProcessWindowLeft t m <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  exact sub_lt_self _
    (Complex.logarithmicPhaseBProcessRadius_pos t ht hm)

theorem Complex.logarithmicPhaseBProcess_center_lt_WindowRight
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Complex.logarithmicPhaseBProcessWindowRight t m := by
  unfold Complex.logarithmicPhaseBProcessWindowRight
  exact lt_add_of_pos_right _
    (Complex.logarithmicPhaseBProcessRadius_pos t ht hm)

theorem Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_radius
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessWindowWidth t m =
      2 * Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessWindowWidth
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  unfold Complex.logarithmicPhaseBProcessWindowRight
  let center := Complex.logarithmicPhaseFourierStationaryPoint t m
  let radius := Complex.logarithmicPhaseBProcessRadius t m
  have hfirst :
      (center + radius) - (center - radius) = radius + radius := by
    calc
      (center + radius) - (center - radius) =
          (center + radius - center) + radius := by
        exact (sub_add (center + radius) center radius).symm
      _ = radius + radius := by
        exact congrArg (fun value : ℝ => value + radius)
          (add_sub_cancel_left center radius)
  exact hfirst.trans (two_mul radius).symm

theorem Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_center_div_scale
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseBProcessWindowWidth t m =
      2 *
        (Complex.logarithmicPhaseFourierStationaryPoint t m /
          Complex.logarithmicPhaseBProcessScale t) := by
  exact
    (Complex.logarithmicPhaseBProcessWindowWidth_eq_two_mul_radius
      t m).trans rfl

theorem Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonModeRange t a ∧
        m < 0 ∧
          (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m ∧
          Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhasePoissonBProcessInteriorModes_subset_modeRange
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ⊆
      Complex.logarithmicPhasePoissonModeRange t a := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhasePoissonBProcessInteriorModes_card_le_modeRange
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact Finset.card_le_card
    (Complex.logarithmicPhasePoissonBProcessInteriorModes_subset_modeRange
      t a b)

theorem Complex.logarithmicPhasePoissonBProcessInteriorModes_subset_activeModes
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ⊆
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  intro m hm
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hradiusNonneg :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmem.2.1
  have hcenterLower :
      (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m :=
    le_trans hmem.2.2.1
      (sub_le_self _ hradiusNonneg)
  have hcenterUpper :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) :=
    le_trans
      (le_add_of_nonneg_right hradiusNonneg)
      hmem.2.2.2
  have htwoThirds : 0 ≤ (2 / 3 : ℝ) :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hleftSupport :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Real.integerBlockCutoffSupportLeftEndpoint
    exact le_trans (sub_le_self (a : ℝ) htwoThirds) hcenterLower
  have hrightSupport :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 :=
    le_trans hcenterUpper (le_add_of_nonneg_right htwoThirds)
  exact
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
      (And.intro hmem.1
        (And.intro hmem.2.1
          (And.intro hleftSupport hrightSupport)))

def Complex.logarithmicPhasePoissonBProcessEndpointModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonActiveModes t a b \
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b

theorem Complex.logarithmicPhasePoissonBProcessInterior_union_endpoint_eq_active
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessEndpointModes t a b =
      Complex.logarithmicPhasePoissonActiveModes t a b := by
  unfold Complex.logarithmicPhasePoissonBProcessEndpointModes
  exact
    (Finset.union_comm _ _).trans
      (Finset.sdiff_union_of_subset
        (Complex.logarithmicPhasePoissonBProcessInteriorModes_subset_activeModes
          t ht a b))

theorem Complex.logarithmicPhasePoissonBProcessInterior_disjoint_endpoint
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b)
      (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) := by
  unfold Complex.logarithmicPhasePoissonBProcessEndpointModes
  exact Finset.disjoint_sdiff

end

end LFunctions
end Boundary
