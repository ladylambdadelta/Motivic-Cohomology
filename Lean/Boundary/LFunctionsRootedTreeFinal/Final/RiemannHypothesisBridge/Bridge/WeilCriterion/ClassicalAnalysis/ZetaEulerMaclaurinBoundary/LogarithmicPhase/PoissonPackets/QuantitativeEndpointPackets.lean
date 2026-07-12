import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePacketBounds

/-!
# Clipped stationary windows for endpoint-active quantitative packets

Endpoint stationary centers have their natural radius window clipped by the
principal block.  The clipped window remains inside the block and has length
at most twice the radius; this is the central geometric estimate for the
endpoint branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

def Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
    (a : ℤ)
    (center radius : ℝ) : ℝ :=
  max (a : ℝ) (center - radius)

def Complex.logarithmicPhaseQuantitativeEndpointWindowRight
    (b : ℤ)
    (center radius : ℝ) : ℝ :=
  min (b : ℝ) (center + radius)

def Complex.logarithmicPhaseQuantitativeEndpointWindowWidth
    (a b : ℤ)
    (center radius : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius -
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_blockLeft
    (a : ℤ)
    (center radius : ℝ) :
    (a : ℝ) ≤ Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  exact le_max_left _ _

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_rawLeft
    (a : ℤ)
    (center radius : ℝ) :
    center - radius ≤
      Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  exact le_max_right _ _

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_blockRight
    (b : ℤ)
    (center radius : ℝ) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius ≤ (b : ℝ) := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  exact min_le_left _ _

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_rawRight
    (b : ℤ)
    (center radius : ℝ) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius ≤ center + radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  exact min_le_right _ _

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_eq_blockLeft_or_rawLeft
    (a : ℤ)
    (center radius : ℝ) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius = (a : ℝ) ∨
      Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius = center - radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  match le_total (a : ℝ) (center - radius) with
  | Or.inl h =>
      exact Or.inr (max_eq_right h)
  | Or.inr h =>
      exact Or.inl (max_eq_left h)

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowRight_eq_blockRight_or_rawRight
    (b : ℤ)
    (center radius : ℝ) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius = (b : ℝ) ∨
      Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius = center + radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  match le_total (b : ℝ) (center + radius) with
  | Or.inl h =>
      exact Or.inl (min_eq_left h)
  | Or.inr h =>
      exact Or.inr (min_eq_right h)

theorem Complex.intervalIntegral_realPhaseOscillation_eq_zero_of_leftClippedAtBlockLeft
    (φ : ℝ → ℝ)
    (a : ℤ)
    (center radius : ℝ)
    (hleft :
      Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius = (a : ℝ)) :
    (∫ x in (a : ℝ)..
      Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius,
      Complex.realPhaseOscillation φ x) = 0 := by
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        (∫ x in (a : ℝ)..right, Complex.realPhaseOscillation φ x) = 0)
      hleft
      (intervalIntegral.integral_same (a : ℝ) (Complex.realPhaseOscillation φ))

theorem Complex.intervalIntegral_realPhaseOscillation_eq_zero_of_rightClippedAtBlockRight
    (φ : ℝ → ℝ)
    (b : ℤ)
    (center radius : ℝ)
    (hright :
      Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius = (b : ℝ)) :
    (∫ x in Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius..(b : ℝ),
      Complex.realPhaseOscillation φ x) = 0 := by
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        (∫ x in left..(b : ℝ), Complex.realPhaseOscillation φ x) = 0)
      hright
      (intervalIntegral.integral_same (b : ℝ) (Complex.realPhaseOscillation φ))

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowRawLeft_lt_center
    (center radius : ℝ)
    (hradius : 0 < radius) :
    center - radius < center :=
  sub_lt_self center hradius

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowCenter_lt_rawRight
    (center radius : ℝ)
    (hradius : 0 < radius) :
    center < center + radius :=
  lt_add_of_pos_right center hradius

theorem Complex.norm_logarithmicPhaseQuantitativeEndpoint_leftRawTail_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius)
    (hleft :
      Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius = center - radius)
    (hblock : (a : ℝ) ≤ center - radius) :
    ‖∫ x in (a : ℝ)..
        Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
          (center - radius))⁻¹ +
        ((center - radius) - (a : ℝ)) •
          ((‖t‖ / (a : ℝ) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
              (center - radius)) ^ 2) := by
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hright_block : center - radius ≤ (b : ℝ) :=
    le_trans hblock (Int.cast_le.mpr hab)
  have hgap : center - radius <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
    exact hcenter ▸ Complex.logarithmicPhaseQuantitativeEndpointWindowRawLeft_lt_center
      center radius hradius
  have htail :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ) (center - radius)
      ha_real le_rfl hright_block hblock hgap hm
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        ‖∫ x in (a : ℝ)..right,
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x‖ ≤ _)
      hleft
      htail

theorem Complex.norm_logarithmicPhaseQuantitativeEndpoint_rightRawTail_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius)
    (hright :
      Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius = center + radius)
    (hleft_block : (a : ℝ) ≤ center + radius)
    (hblock : center + radius ≤ (b : ℝ)) :
    ‖∫ x in Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      2 * ((2 * Real.pi * (-(m : ℝ))) *
        ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (b : ℝ))⁻¹ +
        ((b : ℝ) - (center + radius)) •
          ((‖t‖ / (center + radius) ^ 2) /
            ((2 * Real.pi * (-(m : ℝ))) *
              ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ)) ^ 2) := by
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hgap : Complex.logarithmicPhaseFourierStationaryPoint t m < center + radius := by
    exact hcenter ▸ Complex.logarithmicPhaseQuantitativeEndpointWindowCenter_lt_rawRight
      center radius hradius
  have htail :=
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m (center + radius) (b : ℝ)
      (lt_of_lt_of_le ha_real hleft_block) hleft_block le_rfl hblock hgap hm
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        ‖∫ x in left..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x‖ ≤ _)
      hright
      htail

theorem Complex.integral_logarithmicPhaseQuantitativeEndpoint_principal_eq_three_parts
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (left right : ℝ)
    (ha : 1 ≤ a)
    (haleft : (a : ℝ) ≤ left)
    (hleft_right : left ≤ right)
    (hrightb : right ≤ (b : ℝ)) :
    (∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x) =
      (∫ x in (a : ℝ)..left,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) +
      (∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) +
      (∫ x in right..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) := by
  let oscillation : ℝ → ℂ :=
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
  have ha_real : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hleft_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m (a : ℝ) left ha_real haleft
  have hcentral_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m left right (lt_of_lt_of_le ha_real haleft) hleft_right
  have hright_integrable :=
    Complex.intervalIntegrable_logarithmicPhase_oscillation
      t ht_nonneg m right (b : ℝ)
      (lt_of_lt_of_le (lt_of_lt_of_le ha_real haleft) hleft_right) hrightb
  have hfirst :
      (∫ x in (a : ℝ)..left, oscillation x) +
          ∫ x in left..right, oscillation x =
        ∫ x in (a : ℝ)..right, oscillation x :=
    intervalIntegral.integral_add_adjacent_intervals hleft_integrable hcentral_integrable
  have hsecond :
      (∫ x in (a : ℝ)..right, oscillation x) +
          ∫ x in right..(b : ℝ), oscillation x =
        ∫ x in (a : ℝ)..(b : ℝ), oscillation x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hleft_integrable.trans hcentral_integrable) hright_integrable
  have hthree :
      (∫ x in (a : ℝ)..left, oscillation x) +
          (∫ x in left..right, oscillation x) +
            (∫ x in right..(b : ℝ), oscillation x) =
        ∫ x in (a : ℝ)..(b : ℝ), oscillation x :=
    (congrArg
      (fun value : ℂ => value + ∫ x in right..(b : ℝ), oscillation x)
      hfirst).trans hsecond
  exact hthree.symm

theorem Complex.norm_logarithmicPhaseQuantitativeEndpoint_principal_le
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (left right center radius : ℝ)
    (ha : 1 ≤ a)
    (haleft : (a : ℝ) ≤ left)
    (hleft_right : left ≤ right)
    (hrightb : right ≤ (b : ℝ))
    {leftBound rightBound : ℝ}
    (hleft :
      ‖∫ x in (a : ℝ)..left,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ leftBound)
    (hright :
      ‖∫ x in right..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ rightBound) :
    (hcentral :
      ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ 2 * radius) →
    ‖∫ x in (a : ℝ)..(b : ℝ),
      Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤ leftBound + 2 * radius + rightBound := by
  have hsplit :=
    Complex.integral_logarithmicPhaseQuantitativeEndpoint_principal_eq_three_parts
      t ht_nonneg a b m left right ha haleft hleft_right hrightb
  have htriangle :
      ‖(∫ x in (a : ℝ)..left,
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x) +
          (∫ x in left..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x) +
          (∫ x in right..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x)‖ ≤
        ‖∫ x in (a : ℝ)..left,
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x‖ +
          ‖∫ x in left..right,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ +
          ‖∫ x in right..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ := by
    have hfirst := norm_add_le
      (∫ x in (a : ℝ)..left,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x)
      ((∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x) +
        ∫ x in right..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x)
    have hsecond := norm_add_le
      (∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x)
      (∫ x in right..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x)
    exact le_trans hfirst (add_le_add_left hsecond _)
  intro hcentral
  have hsum := add_le_add (add_le_add hleft hcentral) hright
  exact
    Eq.subst
      (motive := fun value : ℂ => ‖value‖ ≤ leftBound + 2 * radius + rightBound)
      hsplit.symm
      (le_trans htriangle hsum)

def Complex.logarithmicPhaseQuantitativeEndpointLeftTailBudget
    (t : ℝ)
    (a b m : ℤ)
    (center radius : ℝ) : ℝ :=
  if (a : ℝ) ≤ center - radius then
    2 * ((2 * Real.pi * (-(m : ℝ))) *
      (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
        (center - radius))⁻¹ +
      ((center - radius) - (a : ℝ)) •
        ((‖t‖ / (a : ℝ) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (center - radius)) /
            (center - radius)) ^ 2)
  else 0

theorem Complex.norm_logarithmicPhaseQuantitativeEndpoint_leftTail_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius) :
    ‖∫ x in (a : ℝ)..
        Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseQuantitativeEndpointLeftTailBudget t a b m center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointLeftTailBudget
  match Classical.em ((a : ℝ) ≤ center - radius) with
  | Or.inl hraw =>
      have hleft :
          Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius =
            center - radius := by
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
        exact max_eq_right hraw
      exact
        Complex.norm_logarithmicPhaseQuantitativeEndpoint_leftRawTail_le
          t ht ht_nonneg a b m ha hab hm center radius hcenter hradius hleft hraw
  | Or.inr hraw =>
      have hraw_le : center - radius ≤ (a : ℝ) := le_of_not_ge hraw
      have hleft :
          Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius =
            (a : ℝ) := by
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
        exact max_eq_left hraw_le
      have hzero :=
        Complex.intervalIntegral_realPhaseOscillation_eq_zero_of_leftClippedAtBlockLeft
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m)
          a center radius hleft
      have hnorm :
          ‖∫ x in (a : ℝ)..
              Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius,
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ = 0 :=
        (congrArg norm hzero).trans (norm_zero)
      exact Eq.subst (motive := fun value : ℝ => value ≤ 0) hnorm (le_rfl)

def Complex.logarithmicPhaseQuantitativeEndpointRightTailBudget
    (t : ℝ)
    (a b m : ℤ)
    (center radius : ℝ) : ℝ :=
  if center + radius ≤ (b : ℝ) then
    2 * ((2 * Real.pi * (-(m : ℝ))) *
      ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
        (b : ℝ))⁻¹ +
      ((b : ℝ) - (center + radius)) •
        ((‖t‖ / (center + radius) ^ 2) /
          ((2 * Real.pi * (-(m : ℝ))) *
            ((center + radius) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ)) ^ 2)
  else 0

theorem Complex.norm_logarithmicPhaseQuantitativeEndpoint_rightTail_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m < 0)
    (center radius : ℝ)
    (hcenter : center = Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hradius : 0 < radius)
    (hleft_block : (a : ℝ) ≤ center + radius) :
    ‖∫ x in
        Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius..(b : ℝ),
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤
      Complex.logarithmicPhaseQuantitativeEndpointRightTailBudget t a b m center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointRightTailBudget
  match Classical.em (center + radius ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hright :
          Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius =
            center + radius := by
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
        exact min_eq_right hraw
      exact
        Complex.norm_logarithmicPhaseQuantitativeEndpoint_rightRawTail_le
          t ht ht_nonneg a b m ha hab hm center radius hcenter hradius hright
          hleft_block hraw
  | Or.inr hraw =>
      have hraw_le : (b : ℝ) ≤ center + radius := le_of_not_ge hraw
      have hright :
          Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius =
            (b : ℝ) := by
        unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
        exact min_eq_left hraw_le
      have hzero :=
        Complex.intervalIntegral_realPhaseOscillation_eq_zero_of_rightClippedAtBlockRight
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m)
          b center radius hright
      have hnorm :
          ‖∫ x in
              Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x‖ = 0 :=
        (congrArg norm hzero).trans (norm_zero)
      exact Eq.subst (motive := fun value : ℝ => value ≤ 0) hnorm (le_rfl)

theorem Complex.logarithmicPhaseQuantitativeEndpointWindow_nonempty
    (a b : ℤ)
    (center radius : ℝ)
    (hcenter : center ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hradius : 0 ≤ radius) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius ≤
      Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowLeft
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowRight
  exact
    max_le
      (le_min
        (le_trans hcenter.1 hcenter.2)
        (le_trans hcenter.1 (le_add_of_nonneg_right hradius)))
      (le_min
        (le_trans (sub_le_self center hradius) hcenter.2)
        (le_trans
          (sub_le_self center hradius)
          (le_add_of_nonneg_right hradius)))

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowWidth_nonneg
    (a b : ℤ)
    (center radius : ℝ)
    (hcenter : center ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hradius : 0 ≤ radius) :
    0 ≤ Complex.logarithmicPhaseQuantitativeEndpointWindowWidth a b center radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowWidth
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseQuantitativeEndpointWindow_nonempty
      a b center radius hcenter hradius)

theorem Complex.logarithmicPhaseQuantitativeEndpointWindowWidth_le_two_radius
    (a b : ℤ)
    (center radius : ℝ) :
    Complex.logarithmicPhaseQuantitativeEndpointWindowWidth a b center radius ≤
      2 * radius := by
  unfold Complex.logarithmicPhaseQuantitativeEndpointWindowWidth
  have hleft :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_rawLeft
      a center radius
  have hright :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_rawRight
      b center radius
  have hsub :
      Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius -
          Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius ≤
        (center + radius) - (center - radius) :=
    sub_le_sub hright hleft
  have hwidth : (center + radius) - (center - radius) = 2 * radius := by
    calc
      (center + radius) - (center - radius) =
          center + radius + -(center - radius) :=
        sub_eq_add_neg _ _
      _ = center + radius + (-center + radius) :=
        congrArg (fun value : ℝ => center + radius + value)
          ((neg_sub _ _).trans
            ((sub_eq_add_neg _ _).trans (add_comm _ _)))
      _ = (center + -center) + (radius + radius) := by
        calc
          center + radius + (-center + radius) =
              center + (radius + (-center + radius)) := add_assoc center radius (-center + radius)
          _ = center + ((radius + -center) + radius) :=
            congrArg (fun value : ℝ => center + value) (add_assoc radius (-center) radius).symm
          _ = center + ((-center + radius) + radius) :=
            congrArg (fun value : ℝ => center + (value + radius)) (add_comm radius (-center))
          _ = center + (-center + (radius + radius)) :=
            congrArg (fun value : ℝ => center + value) (add_assoc (-center) radius radius)
          _ = (center + -center) + (radius + radius) :=
            (add_assoc center (-center) (radius + radius)).symm
      _ = 0 + (radius + radius) :=
        congrArg (fun value : ℝ => value + (radius + radius)) (add_neg_cancel center)
      _ = radius + radius := zero_add (radius + radius)
      _ = 2 * radius := (two_mul radius).symm
  exact hsub.trans_eq hwidth

theorem Complex.norm_intervalIntegral_realPhaseOscillation_le_length
    (φ : ℝ → ℝ)
    (left right : ℝ)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right, Complex.realPhaseOscillation φ x‖ ≤ right - left := by
  have hpointwise :
      ∀ x ∈ Ι left right, ‖Complex.realPhaseOscillation φ x‖ ≤ (1 : ℝ) :=
    fun x _hx => le_of_eq (Complex.norm_realPhaseOscillation φ x)
  have hraw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := left) (b := right)
      (f := Complex.realPhaseOscillation φ) (C := 1) hpointwise
  have hlength : (1 : ℝ) * |right - left| = right - left := by
    calc
      (1 : ℝ) * |right - left| = |right - left| := one_mul _
      _ = right - left := abs_of_nonneg (sub_nonneg.mpr hleft_right)
  exact
    Eq.subst
      (motive := fun bound : ℝ =>
        ‖∫ x in left..right, Complex.realPhaseOscillation φ x‖ ≤ bound)
      hlength
      hraw

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointCentral_le_two_radius
    (t : ℝ)
    (a b m : ℤ)
    (center radius : ℝ)
    (hcenter : center ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hradius : 0 ≤ radius) :
    ‖∫ x in
        Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius..
          Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m) x‖ ≤ 2 * radius := by
  have horder :=
    Complex.logarithmicPhaseQuantitativeEndpointWindow_nonempty
      a b center radius hcenter hradius
  have hlength :=
    Complex.norm_intervalIntegral_realPhaseOscillation_le_length
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
      (Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius)
      (Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius)
      horder
  have hwidth :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowWidth_le_two_radius
      a b center radius
  exact le_trans hlength hwidth

end
end LFunctions
end Boundary
