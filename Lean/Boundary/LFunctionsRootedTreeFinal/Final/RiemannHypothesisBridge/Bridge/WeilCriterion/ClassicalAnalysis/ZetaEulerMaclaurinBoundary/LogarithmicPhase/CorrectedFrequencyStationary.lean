import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.NonstationaryPhase
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FiniteBProcess
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.Derivatives

/-!
# Correct Fourier stationary points for the logarithmic phase

The exponential convention in the finite B-process is `exp (I * φ(x))`.
Consequently the stationary equation for the integer mode `m` is
`φ'(x) = 2πm`.  This owner file records the resulting logarithmic stationary
point, keeping it distinct from the older raw-derivative packet index.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Complex.nonnegative_div_sq_le_of_le
    {A d₀ d : ℝ}
    (hA : 0 ≤ A)
    (hd₀ : 0 < d₀)
    (hdd : d₀ ≤ d) :
    A / d ^ 2 ≤ A / d₀ ^ 2 := by
  have hd : 0 < d := lt_of_lt_of_le hd₀ hdd
  have hsq : d₀ ^ 2 ≤ d ^ 2 :=
    sq_le_sq.mpr
      (by
        calc
          |d₀| = d₀ := abs_of_pos hd₀
          _ ≤ d := hdd
          _ = |d| := (abs_of_pos hd).symm)
  exact div_le_div_of_nonneg_left hA (sq_pos_of_pos hd₀) hsq

/-- Stationary point for the logarithmic phase and the actual Fourier mode
`m`, in the negative-frequency branch. -/
def Complex.logarithmicPhaseFourierStationaryPoint
    (t : ℝ)
    (m : ℤ) : ℝ :=
  ‖t‖ / (2 * Real.pi * (-(m : ℝ)))

theorem Complex.logarithmicPhaseAngular_mul_stationaryCenter
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        Complex.logarithmicPhaseFourierStationaryPoint t m =
      ‖t‖ := by
  have hmCastRaw : (m : ℝ) < ((0 : ℤ) : ℝ) := Int.cast_lt.mpr hm
  have hmCast : (m : ℝ) < 0 :=
    Eq.mp
      (congrArg (fun value : ℝ => (m : ℝ) < value) Int.cast_zero)
      hmCastRaw
  have hmNegative : 0 < -(m : ℝ) := neg_pos.mpr hmCast
  have hangular : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    mul_pos (mul_pos zero_lt_two Real.pi_pos) hmNegative
  have hangularNe : (2 * Real.pi * (-(m : ℝ))) ≠ 0 :=
    ne_of_gt hangular
  unfold Complex.logarithmicPhaseFourierStationaryPoint
  exact Eq.trans
    (mul_div_assoc
      (2 * Real.pi * (-(m : ℝ))) ‖t‖
      (2 * Real.pi * (-(m : ℝ)))).symm
    (mul_div_cancel_left₀ ‖t‖ hangularNe)

theorem Complex.logarithmicPhaseFourierStationaryDistance_ge_left_endpoint
    {center left right x : ℝ}
    (hcenter : center ≤ left)
    (hx : x ∈ Set.Icc left right) :
    left - center ≤ |x - center| := by
  have hdistance_nonneg : 0 ≤ x - center :=
    sub_nonneg.mpr (le_trans hcenter hx.1)
  have hendpoint_nonneg : 0 ≤ left - center :=
    sub_nonneg.mpr hcenter
  have horder : left - center ≤ x - center :=
    sub_le_sub_right hx.1 center
  exact horder.trans_eq (abs_of_nonneg hdistance_nonneg).symm

theorem Complex.logarithmicPhaseFourierStationaryDistance_ge_right_endpoint
    {center left right x : ℝ}
    (hcenter : right ≤ center)
    (hx : x ∈ Set.Icc left right) :
    center - right ≤ |center - x| := by
  have hdistance_nonneg : 0 ≤ center - x :=
    sub_nonneg.mpr (le_trans hx.2 hcenter)
  have horder : center - right ≤ center - x :=
    sub_le_sub_left hx.2 center
  exact horder.trans_eq (abs_of_nonneg hdistance_nonneg).symm

theorem Complex.frequencyGap_div_right_le_frequencyGap_div_point_of_left_separation
    {q center left right x : ℝ}
    (hq : 0 ≤ q)
    (hcenter : center ≤ left)
    (hleft : 0 < left)
    (hright : left ≤ right)
    (hx : x ∈ Set.Icc left right) :
    q * (left - center) / right ≤ q * |x - center| / x := by
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
  have hdistance_left : left - center ≤ |x - center| :=
    Complex.logarithmicPhaseFourierStationaryDistance_ge_left_endpoint
      hcenter hx
  have hdistance_nonneg : 0 ≤ |x - center| := abs_nonneg _
  have hleft_distance_nonneg : 0 ≤ left - center := sub_nonneg.mpr hcenter
  have hnumerator :
      q * (left - center) ≤ q * |x - center| :=
    mul_le_mul_of_nonneg_left hdistance_left hq
  have hnumerator_nonneg : 0 ≤ q * |x - center| :=
    mul_nonneg hq hdistance_nonneg
  have hproduct_left :
      q * (left - center) * x ≤ q * |x - center| * x :=
    mul_le_mul_of_nonneg_right hnumerator (le_of_lt hx_pos)
  have hproduct_right :
      q * |x - center| * x ≤ q * |x - center| * right :=
    mul_le_mul_of_nonneg_left hx.2 hnumerator_nonneg
  have hproduct :
      q * (left - center) * x ≤ q * |x - center| * right :=
    hproduct_left.trans hproduct_right
  exact
    (div_le_div_iff₀ hright_pos hx_pos).mpr hproduct

theorem Complex.frequencyGap_div_right_le_frequencyGap_div_point_of_right_separation
    {q center left right x : ℝ}
    (hq : 0 ≤ q)
    (hcenter : right ≤ center)
    (hleft : 0 < left)
    (hright : left ≤ right)
    (hx : x ∈ Set.Icc left right) :
    q * (center - right) / right ≤ q * |center - x| / x := by
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
  have hdistance_right : center - right ≤ |center - x| := by
    have hdistance_nonneg : 0 ≤ center - x :=
      sub_nonneg.mpr (le_trans hx.2 hcenter)
    have horder : center - right ≤ center - x :=
      sub_le_sub_left hx.2 center
    exact horder.trans_eq (abs_of_nonneg hdistance_nonneg).symm
  have hnumerator :
      q * (center - right) ≤ q * |center - x| :=
    mul_le_mul_of_nonneg_left hdistance_right hq
  have hnumerator_nonneg : 0 ≤ q * |center - x| :=
    mul_nonneg hq (abs_nonneg _)
  have hproduct_left :
      q * (center - right) * x ≤ q * |center - x| * x :=
    mul_le_mul_of_nonneg_right hnumerator (le_of_lt hx_pos)
  have hproduct_right :
      q * |center - x| * x ≤ q * |center - x| * right :=
    mul_le_mul_of_nonneg_left hx.2 hnumerator_nonneg
  exact
    (div_le_div_iff₀ hright_pos hx_pos).mpr
      (hproduct_left.trans hproduct_right)

/-- Explicit real derivative of the corrected logarithmic Fourier twist on the
positive half-line. -/
def Complex.logarithmicPhaseFourierTwistedDerivative
    (t : ℝ)
    (m : ℤ)
    (x : ℝ) : ℝ :=
  -‖t‖ / x - Real.integerAngularFrequency m

/-- Corrected active Fourier modes met by the block and carrying a stationary
point inside its real endpoint interval. -/
def Complex.logarithmicPhaseFourierActiveModes
    (t : ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Complex.realPhaseDerivativeFrequencyModes
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m ∈
          Set.Icc (a : ℝ) (b : ℝ))

/-- Membership in the corrected stationary active-mode family. -/
theorem Complex.mem_logarithmicPhaseFourierActiveModes_iff
    (t : ℝ)
    (a b : ℕ)
    (m : ℤ) :
    m ∈ Complex.logarithmicPhaseFourierActiveModes t a b ↔
      m ∈ Complex.realPhaseDerivativeFrequencyModes
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b ∧
        m < 0 ∧
          Complex.logarithmicPhaseFourierStationaryPoint t m ∈
            Set.Icc (a : ℝ) (b : ℝ) := by
  exact Finset.mem_filter

/-- Corrected stationary active modes form a subset of the finite derivative
mode family. -/
theorem Complex.logarithmicPhaseFourierActiveModes_subset_modes
    (t : ℝ)
    (a b : ℕ) :
    Complex.logarithmicPhaseFourierActiveModes t a b ⊆
      Complex.realPhaseDerivativeFrequencyModes
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b := by
  exact Finset.filter_subset _ _

/-- The corrected active stationary-center count is bounded by the block
cardinality. -/
theorem Complex.logarithmicPhaseFourierActiveModes_card_le_block_card
    (t : ℝ)
    (a b : ℕ) :
    (Complex.logarithmicPhaseFourierActiveModes t a b).card ≤
      (Finset.Icc a b).card := by
  exact
    le_trans
      (Finset.card_le_card
        (Complex.logarithmicPhaseFourierActiveModes_subset_modes t a b))
      (Complex.realPhaseDerivativeFrequencyModes_card_le_block_card
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b)

/-- The denominator in the corrected logarithmic stationary point is positive
for a negative Fourier mode. -/
theorem Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos
    (m : ℤ)
    (hm : m < 0) :
    0 < 2 * Real.pi * (-(m : ℝ)) := by
  have hm_real : (m : ℝ) < 0 :=
    Eq.subst
      (motive := fun value : ℝ => (m : ℝ) < value)
      Int.cast_zero
      (Int.cast_lt.mpr hm)
  have hmode : 0 < -(m : ℝ) :=
    neg_pos.mpr hm_real
  exact mul_pos (mul_pos zero_lt_two Real.pi_pos) hmode

theorem Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m x =
      (2 * Real.pi * (-(m : ℝ))) *
        (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hq : 2 * Real.pi * (-(m : ℝ)) ≠ 0 :=
    ne_of_gt (Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm)
  have hcenter :
      (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhaseFourierStationaryPoint t m = ‖t‖ := by
    unfold Complex.logarithmicPhaseFourierStationaryPoint
    exact mul_div_cancel₀ ‖t‖ hq
  change -‖t‖ / x - 2 * Real.pi * (m : ℝ) =
    (2 * Real.pi * (-(m : ℝ))) *
      (x - ‖t‖ / (2 * Real.pi * (-(m : ℝ)))) / x
  refine (eq_div_iff hx_ne).mpr ?_
  have hleft :
      (-‖t‖ / x - 2 * Real.pi * (m : ℝ)) * x =
        (2 * Real.pi * (-(m : ℝ))) * x - ‖t‖ := by
    have hmode : -(2 * Real.pi * (m : ℝ)) = 2 * Real.pi * (-(m : ℝ)) :=
      (mul_neg (2 * Real.pi) (m : ℝ)).symm
    have horder :
        -‖t‖ / x + 2 * Real.pi * (-(m : ℝ)) =
          2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x := by
      calc
        -‖t‖ / x + 2 * Real.pi * (-(m : ℝ)) =
            2 * Real.pi * (-(m : ℝ)) + (-‖t‖ / x) :=
          add_comm _ _
        _ = 2 * Real.pi * (-(m : ℝ)) + -(‖t‖ / x) :=
            congrArg (fun value : ℝ => 2 * Real.pi * (-(m : ℝ)) + value)
            (neg_div x ‖t‖)
        _ = 2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x := rfl
    calc
      (-‖t‖ / x - 2 * Real.pi * (m : ℝ)) * x =
          (-‖t‖ / x + 2 * Real.pi * (-(m : ℝ))) * x := by
            exact congrArg (fun value : ℝ => (-‖t‖ / x + value) * x) hmode
      _ = (2 * Real.pi * (-(m : ℝ)) - ‖t‖ / x) * x :=
        congrArg (fun value : ℝ => value * x) horder
      _ = (2 * Real.pi * (-(m : ℝ))) * x - (‖t‖ / x) * x :=
        sub_mul _ _ _
      _ = (2 * Real.pi * (-(m : ℝ))) * x - ‖t‖ :=
        congrArg (fun value : ℝ => (2 * Real.pi * (-(m : ℝ))) * x - value)
          (div_mul_cancel₀ ‖t‖ hx_ne)
  have hright :
      (2 * Real.pi * (-(m : ℝ))) *
          (x - ‖t‖ / (2 * Real.pi * (-(m : ℝ)))) =
        (2 * Real.pi * (-(m : ℝ))) * x - ‖t‖ := by
    calc
      _ = (2 * Real.pi * (-(m : ℝ))) * x -
          (2 * Real.pi * (-(m : ℝ))) *
            (‖t‖ / (2 * Real.pi * (-(m : ℝ)))) := mul_sub _ _ _
      _ = (2 * Real.pi * (-(m : ℝ))) * x - ‖t‖ :=
        congrArg (fun value : ℝ => (2 * Real.pi * (-(m : ℝ))) * x - value)
          (mul_div_cancel₀ ‖t‖ hq)
  exact hleft.trans hright.symm

/- The explicit gap identity gives the sign of the derivative on either side
of the actual stationary point.  This is the separation fact used when a
packet is assigned to a nonstationary complement. -/
theorem Complex.logarithmicPhaseFourierTwistedDerivative_neg_of_lt_stationaryPoint
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x)
    (hbelow : x < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m x < 0 := by
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hdistance :
      x - Complex.logarithmicPhaseFourierStationaryPoint t m < 0 :=
    sub_neg.mpr hbelow
  have hproduct :
      2 * Real.pi * (-(m : ℝ)) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) < 0 :=
    mul_neg_of_pos_of_neg hq_pos hdistance
  have hquotient :
      2 * Real.pi * (-(m : ℝ)) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x < 0 :=
    div_neg_of_neg_of_pos hproduct hx
  exact
    Eq.subst
      (motive := fun value : ℝ => value < 0)
      (Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
        t hm hx).symm
      hquotient

theorem Complex.logarithmicPhaseFourierTwistedDerivative_pos_of_gt_stationaryPoint
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x)
    (habove : Complex.logarithmicPhaseFourierStationaryPoint t m < x) :
    0 < Complex.logarithmicPhaseFourierTwistedDerivative t m x := by
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hdistance :
      0 < x - Complex.logarithmicPhaseFourierStationaryPoint t m :=
    sub_pos.mpr habove
  have hproduct :
      0 < 2 * Real.pi * (-(m : ℝ)) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) :=
    mul_pos hq_pos hdistance
  have hquotient :
      0 < 2 * Real.pi * (-(m : ℝ)) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x :=
    div_pos hproduct hx
  exact
    Eq.subst
      (motive := fun value : ℝ => 0 < value)
      (Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
        t hm hx).symm
      hquotient

theorem Complex.logarithmicPhaseFourierStationaryPoint_ne_of_lt
    (t : ℝ)
    {m : ℤ}
    {x : ℝ}
    (hbelow : x < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m :=
  ne_of_lt hbelow

theorem Complex.logarithmicPhaseFourierStationaryPoint_ne_of_gt
    (t : ℝ)
    {m : ℤ}
    {x : ℝ}
    (habove : Complex.logarithmicPhaseFourierStationaryPoint t m < x) :
    x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m :=
  ne_of_gt habove

/-- The canonical derivative-frequency mode of a positive logarithmic sample
lies in the negative Fourier branch. -/
theorem Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_neg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {n : ℕ}
    (hn : 1 ≤ n) :
    Complex.realPhaseDerivativeFrequencyMode
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      n ≤ -1 := by
  have ht_pos : 0 < t :=
    lt_of_lt_of_le zero_lt_one
      (Eq.subst
        (motive := fun value : ℝ => 1 ≤ value)
        (Real.norm_of_nonneg ht_nonneg)
        ht)
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hn)
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (n : ℝ) = -t / (n : ℝ) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
      t hn_pos
  have hderiv_neg :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (n : ℝ) < 0 := by
    have hquotient_neg : -t / (n : ℝ) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos ht_pos) hn_pos
    exact hderiv.trans_lt hquotient_neg
  have hfrequency_pos : 0 < 2 * Real.pi :=
    mul_pos zero_lt_two Real.pi_pos
  have hratio_neg :
      deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n : ℝ) /
        (2 * Real.pi) < 0 :=
    div_neg_of_neg_of_pos hderiv_neg hfrequency_pos
  exact
    Int.floor_le_neg_one_iff.mpr hratio_neg

/-- Canonical logarithmic derivative-frequency modes are bounded below by the
left-endpoint derivative floor on an integer block. -/
theorem Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_ge_left_floor
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    (ha : 1 ≤ a)
    (hn : n ∈ Finset.Icc a b) :
    Int.floor
        ((-‖t‖ / (a : ℝ)) / (2 * Real.pi)) ≤
      Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        n := by
  have ha_pos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hn_pos : 0 < (n : ℝ) :=
    lt_of_lt_of_le ha_pos (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1)
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hreciprocal :
      ((n : ℝ)⁻¹) ≤ ((a : ℝ)⁻¹) := by
    exact
      inv_anti₀ ha_pos (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1)
  have hscale :
      ‖t‖ * ((n : ℝ)⁻¹) ≤ ‖t‖ * ((a : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hreciprocal hT_nonneg
  have hquotient :
      ‖t‖ / (n : ℝ) ≤ ‖t‖ / (a : ℝ) := by
    exact
      Eq.subst
        (motive := fun value : ℝ => value ≤ ‖t‖ / (a : ℝ))
        (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
        (Eq.subst
          (motive := fun value : ℝ => ‖t‖ * ((n : ℝ)⁻¹) ≤ value)
          (div_eq_mul_inv ‖t‖ (a : ℝ)).symm
          hscale)
  have hnegative_quotient :
      -‖t‖ / (a : ℝ) ≤ -‖t‖ / (n : ℝ) := by
    calc
      -‖t‖ / (a : ℝ) = -(‖t‖ / (a : ℝ)) :=
        neg_div (a : ℝ) ‖t‖
      _ ≤ -(‖t‖ / (n : ℝ)) := neg_le_neg hquotient
      _ = -‖t‖ / (n : ℝ) := neg_div' (n : ℝ) ‖t‖
  have htwo_pi_pos : 0 < 2 * Real.pi :=
    mul_pos zero_lt_two Real.pi_pos
  have hfrequency_order :
      (-‖t‖ / (a : ℝ)) / (2 * Real.pi) ≤
        (-‖t‖ / (n : ℝ)) / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hnegative_quotient htwo_pi_pos.le
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (n : ℝ) = -‖t‖ / (n : ℝ) := by
    have hbase :
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n : ℝ) = -t / (n : ℝ) :=
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
        t hn_pos
    exact
      hbase.trans
        (congrArg (fun value : ℝ => -value / (n : ℝ))
          (Real.norm_of_nonneg ht_nonneg).symm)
  have hmode_argument :
      deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n : ℝ) / (2 * Real.pi) =
        (-‖t‖ / (n : ℝ)) / (2 * Real.pi) :=
    congrArg (fun value : ℝ => value / (2 * Real.pi)) hderiv
  exact
    (Int.floor_mono hfrequency_order).trans_eq
      (congrArg Int.floor hmode_argument.symm)

/-- The canonical logarithmic derivative-frequency assignment is monotone on
every positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ∀ {i j : ℕ},
      i ∈ Finset.Icc a b →
        j ∈ Finset.Icc a b →
          i ≤ j →
            Complex.realPhaseDerivativeFrequencyMode
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                i ≤
              Complex.realPhaseDerivativeFrequencyMode
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                j := by
  intro i j hi hj hij
  have ha_pos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hi_pos : 0 < (i : ℝ) :=
    lt_of_lt_of_le ha_pos (Nat.cast_le.mpr (Finset.mem_Icc.mp hi).1)
  have hj_pos : 0 < (j : ℝ) :=
    lt_of_lt_of_le hi_pos (Nat.cast_le.mpr hij)
  have hinv : ((j : ℝ)⁻¹) ≤ ((i : ℝ)⁻¹) :=
    inv_anti₀ hi_pos (Nat.cast_le.mpr hij)
  have hscale :
      ‖t‖ * ((j : ℝ)⁻¹) ≤ ‖t‖ * ((i : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hinv (norm_nonneg t)
  have hnegative :
      -(‖t‖ * ((i : ℝ)⁻¹)) ≤ -(‖t‖ * ((j : ℝ)⁻¹)) :=
    neg_le_neg hscale
  have hquotient :
      -‖t‖ / (i : ℝ) ≤ -‖t‖ / (j : ℝ) := by
    calc
      -‖t‖ / (i : ℝ) = -(‖t‖ / (i : ℝ)) :=
        neg_div (i : ℝ) ‖t‖
      _ = -(‖t‖ * ((i : ℝ)⁻¹)) :=
        congrArg Neg.neg (div_eq_mul_inv ‖t‖ (i : ℝ))
      _ ≤ -(‖t‖ * ((j : ℝ)⁻¹)) := hnegative
      _ = -(‖t‖ / (j : ℝ)) :=
        congrArg Neg.neg (div_eq_mul_inv ‖t‖ (j : ℝ)).symm
      _ = -‖t‖ / (j : ℝ) := neg_div' (j : ℝ) ‖t‖
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    le_of_lt (mul_pos zero_lt_two Real.pi_pos)
  have hfrequency :
      (-‖t‖ / (i : ℝ)) / (2 * Real.pi) ≤
        (-‖t‖ / (j : ℝ)) / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hquotient htwo_pi_nonneg
  have hderiv_i :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (i : ℝ) = -‖t‖ / (i : ℝ) := by
    exact
      Eq.trans
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
          t hi_pos)
        (congrArg (fun value : ℝ => -value / (i : ℝ))
          (Real.norm_of_nonneg ht_nonneg).symm)
  have hderiv_j :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (j : ℝ) = -‖t‖ / (j : ℝ) := by
    exact
      Eq.trans
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
          t hj_pos)
        (congrArg (fun value : ℝ => -value / (j : ℝ))
          (Real.norm_of_nonneg ht_nonneg).symm)
  have hfloor := Int.floor_mono hfrequency
  exact
    Eq.subst
      (motive := fun left : ℤ =>
        left ≤
          Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) j)
      (congrArg Int.floor
        (congrArg (fun value : ℝ => value / (2 * Real.pi)) hderiv_i)).symm
      (Eq.subst
        (motive := fun right : ℤ =>
          ⌊(-‖t‖ / (i : ℝ)) / (2 * Real.pi)⌋ ≤ right)
        (congrArg Int.floor
          (congrArg (fun value : ℝ => value / (2 * Real.pi)) hderiv_j)).symm
        hfloor)

/-- Corrected logarithmic resonance windows are strictly ordered by their
Fourier-mode labels. -/
theorem Complex.logarithmicPhaseRealPhase_frequencyPacket_ordered
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m₁ m₂ : ℤ}
    (hmodes : m₁ < m₂) :
    ∀ i ∈ Complex.frequencyPacket a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m₁,
      ∀ j ∈ Complex.frequencyPacket a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m₂,
        i < j := by
  exact
    Complex.frequencyPacket_ordered_of_monotoneOn
      a b
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      (Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
        t ht_nonneg ha)
      hmodes

/-- Each canonical logarithmic derivative-frequency packet is interval
connected on a positive integer block. -/
theorem Complex.logarithmicPhaseRealPhase_frequencyPacket_intervalConnected
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (m : ℤ) :
    ∀ i j k : ℕ,
      i ∈ Complex.frequencyPacket a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m →
        k ∈ Complex.frequencyPacket a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m →
          j ∈ Finset.Icc a b →
            i ≤ j → j ≤ k →
              j ∈ Complex.frequencyPacket a b
                (Complex.realPhaseDerivativeFrequencyMode
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t))
                m := by
  exact
    Complex.frequencyPacket_intervalConnected_of_monotoneOn
      a b
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      m
      (Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
        t ht_nonneg ha)

/-- Every canonical logarithmic derivative-frequency packet is a half-open
integer interval with endpoints inside the successor block. -/
theorem Complex.logarithmicPhaseRealPhase_frequencyPacket_exists_eq_Ico
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (m : ℤ) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.frequencyPacket a b
            (Complex.realPhaseDerivativeFrequencyMode
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            m =
          Finset.Ico c d := by
  exact
    Complex.frequencyPacket_exists_eq_Ico_of_monotoneOn
      hab
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      m
      (Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
        t ht_nonneg ha)

/-- Each corrected logarithmic active window has canonical interval endpoints
and its stationary packet contribution is bounded by their ambient spread. -/
theorem Complex.logarithmicPhaseRealPhase_frequencyPacket_activeWindow_bound
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (m : ℤ) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.frequencyPacket a b
            (Complex.realPhaseDerivativeFrequencyMode
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            m = Finset.Ico c d ∧
        ‖Complex.frequencyPacketTwistedSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b
            (Complex.realPhaseDerivativeFrequencyMode
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            m‖ ≤ (((b + 1) - a : ℕ) : ℝ) := by
  exact
    Complex.exists_frequencyPacket_Ico_and_norm_le_blockLength_of_monotoneOn
      (φ :=
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      hab
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      m
      (Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
        t ht_nonneg ha)

/-- The corrected stationary contribution is bounded by the number of active
centers times the canonical ambient endpoint spread. -/
theorem Complex.logarithmicPhaseFourierActiveModes_sum_le_card_mul_blockLength
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ m ∈ Complex.logarithmicPhaseFourierActiveModes t a b,
        Complex.frequencyPacketTwistedSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m‖ ≤
      ((Complex.logarithmicPhaseFourierActiveModes t a b).card : ℝ) *
        (((b + 1) - a : ℕ) : ℝ) := by
  have hlength_nonneg :
      0 ≤ (((b + 1) - a : ℕ) : ℝ) :=
    Nat.cast_nonneg ((b + 1) - a)
  have hpacket :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseFourierActiveModes t a b →
          ‖Complex.frequencyPacketTwistedSum
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b
              (Complex.realPhaseDerivativeFrequencyMode
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
              m‖ ≤ (((b + 1) - a : ℕ) : ℝ) := by
    intro m _hm
    match
        Complex.logarithmicPhaseRealPhase_frequencyPacket_activeWindow_bound
          t ht_nonneg ha hab m with
    | ⟨_c, _d, _hac, _hcd, _hdb, _hpacket, hnorm⟩ =>
        exact hnorm
  exact
    Complex.norm_selectedFrequencyPacketSums_le_card_mul
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      (Complex.logarithmicPhaseFourierActiveModes t a b)
      (((b + 1) - a : ℕ) : ℝ)
      hlength_nonneg hpacket

/-- Finite active-center cardinality eliminates the mode count from the
stationary-window sum. -/
theorem Complex.logarithmicPhaseFourierActiveModes_sum_le_blockCard_mul_blockLength
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ m ∈ Complex.logarithmicPhaseFourierActiveModes t a b,
        Complex.frequencyPacketTwistedSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          m‖ ≤
      ((Finset.Icc a b).card : ℝ) *
        (((b + 1) - a : ℕ) : ℝ) := by
  have hactive :=
    Complex.logarithmicPhaseFourierActiveModes_sum_le_card_mul_blockLength
      t ht_nonneg ha hab
  have hcard_nat :
      (Complex.logarithmicPhaseFourierActiveModes t a b).card ≤
        (Finset.Icc a b).card :=
    Complex.logarithmicPhaseFourierActiveModes_card_le_block_card t a b
  have hcard_real :
      ((Complex.logarithmicPhaseFourierActiveModes t a b).card : ℝ) ≤
        ((Finset.Icc a b).card : ℝ) :=
    Nat.cast_le.mpr hcard_nat
  have hlength_nonneg :
      0 ≤ (((b + 1) - a : ℕ) : ℝ) :=
    Nat.cast_nonneg ((b + 1) - a)
  have hproduct :
      ((Complex.logarithmicPhaseFourierActiveModes t a b).card : ℝ) *
          (((b + 1) - a : ℕ) : ℝ) ≤
        ((Finset.Icc a b).card : ℝ) *
          (((b + 1) - a : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hcard_real hlength_nonneg
  exact le_trans hactive hproduct

/-- Canonical complement gaps for the corrected active stationary modes are
interval connected. -/
theorem Complex.logarithmicPhaseFourierActiveComplementGap_intervalConnected
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (r : ℕ) :
    ∀ i j k : ℕ,
      i ∈ Complex.frequencyPacketComplementGap a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          (Complex.logarithmicPhaseFourierActiveModes t a b) r →
        k ∈ Complex.frequencyPacketComplementGap a b
          (Complex.realPhaseDerivativeFrequencyMode
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
          (Complex.logarithmicPhaseFourierActiveModes t a b) r →
          j ∈ Complex.frequencyPacketFamilyComplement a b
            (Complex.realPhaseDerivativeFrequencyMode
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
            (Complex.logarithmicPhaseFourierActiveModes t a b) →
            i ≤ j → j ≤ k →
              j ∈ Complex.frequencyPacketComplementGap a b
                (Complex.realPhaseDerivativeFrequencyMode
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                    t))
                (Complex.logarithmicPhaseFourierActiveModes t a b) r := by
  exact
    Complex.frequencyPacketComplementGap_intervalConnected_of_monotoneOn
      a b
      (Complex.realPhaseDerivativeFrequencyMode
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t))
      (Complex.logarithmicPhaseFourierActiveModes t a b)
      r
      (Complex.logarithmicPhaseRealPhase_derivativeFrequencyMode_monotoneOn
        t ht_nonneg ha)

/-- Corrected logarithmic stationary points are positive for nonzero `t`. -/
theorem Complex.logarithmicPhaseFourierStationaryPoint_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℤ}
    (hm : m < 0) :
    0 < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  exact
    div_pos ht_pos
      (Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm)

/-- The negative Fourier angular frequency is the phase norm divided by its
corrected stationary center. -/
theorem Complex.logarithmicPhaseAngular_eq_norm_div_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    2 * Real.pi * (-(m : ℝ)) =
      ‖t‖ / Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hcenter :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hproduct :=
    Complex.logarithmicPhaseAngular_mul_stationaryCenter t hm
  exact (eq_div_iff (ne_of_gt hcenter)).mpr hproduct

/-- Reciprocal cancellation with the actual angular frequency. -/
theorem Real.logarithmicPhase_fourier_reciprocal_identity
    {T μ : ℝ}
    (hT : 0 < T)
    (hμ : 0 < μ) :
    T / (T / μ) = μ := by
  have hT_ne : T ≠ 0 := ne_of_gt hT
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  calc
    T / (T / μ) = T * (T / μ)⁻¹ :=
      div_eq_mul_inv T (T / μ)
    _ = T * (T * μ⁻¹)⁻¹ := by
      exact congrArg (fun value : ℝ => T * value⁻¹)
        (div_eq_mul_inv T μ)
    _ = T * ((μ⁻¹)⁻¹ * T⁻¹) := by
      exact congrArg (fun value : ℝ => T * value)
        (mul_inv_rev T μ⁻¹)
    _ = T * (μ * T⁻¹) := by
      exact congrArg (fun value : ℝ => T * (value * T⁻¹))
        (inv_inv μ)
    _ = μ * (T * T⁻¹) := by
      calc
        T * (μ * T⁻¹) = (T * μ) * T⁻¹ :=
          (mul_assoc T μ T⁻¹).symm
        _ = (μ * T) * T⁻¹ :=
          congrArg (fun value : ℝ => value * T⁻¹) (mul_comm T μ)
        _ = μ * (T * T⁻¹) :=
          mul_assoc μ T T⁻¹
    _ = μ * 1 :=
      congrArg (fun value : ℝ => μ * value) (mul_inv_cancel₀ hT_ne)
    _ = μ := mul_one μ

/-- The logarithmic derivative at the corrected Fourier stationary point is
exactly the angular frequency `2πm`. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_fourierStationaryPoint_eq
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {m : ℤ}
    (hm : m < 0) :
    deriv
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Complex.logarithmicPhaseFourierStationaryPoint t m) =
      Real.integerAngularFrequency m := by
  let x : ℝ := Complex.logarithmicPhaseFourierStationaryPoint t m
  have hx_pos : 0 < x :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hderiv :
      deriv
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -‖t‖ / x :=
    have hbase :
        deriv
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
          -t / x :=
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
        t hx_pos
    have hnorm : ‖t‖ = t :=
      Real.norm_of_nonneg ht_nonneg
    hbase.trans
      (congrArg (fun value : ℝ => -value / x) hnorm.symm)
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hμ_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hrecip :
      ‖t‖ / x = 2 * Real.pi * (-(m : ℝ)) := by
    show
      ‖t‖ /
          (‖t‖ / (2 * Real.pi * (-(m : ℝ)))) =
        2 * Real.pi * (-(m : ℝ))
    exact
      Real.logarithmicPhase_fourier_reciprocal_identity
        hT_pos hμ_pos
  have hnegative :
      -(‖t‖ / x) = 2 * Real.pi * (m : ℝ) := by
    calc
      -(‖t‖ / x) = -(2 * Real.pi * (-(m : ℝ))) :=
        congrArg Neg.neg hrecip
      _ = 2 * Real.pi * (m : ℝ) := by
        calc
          -(2 * Real.pi * (-(m : ℝ))) =
              (2 * Real.pi) * (-(-(m : ℝ))) :=
            (mul_neg (2 * Real.pi) (-(m : ℝ))).symm
          _ = (2 * Real.pi) * (m : ℝ) := by
            exact congrArg (fun value : ℝ => (2 * Real.pi) * value)
              (neg_neg (m : ℝ))
  have hangular :
      2 * Real.pi * (m : ℝ) = Real.integerAngularFrequency m :=
    rfl
  exact
    hderiv.trans
      ((neg_div x ‖t‖).trans (hnegative.trans hangular))

/-- Second derivative of the positive-real logarithmic phase, exposed as a
`HasDerivAt` theorem for the nonstationary reciprocal coefficient. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => -t / y)
      (t / x ^ 2)
      x := by
  have hinverse :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv hx.ne'
  have hraw :
      HasDerivAt
        (fun y : ℝ => (-t) * y⁻¹)
        ((-t) * (-(x ^ 2)⁻¹))
        x :=
    hinverse.const_mul (-t)
  have hfunction :
      (fun y : ℝ => (-t) * y⁻¹) = (fun y : ℝ => -t / y) := by
    funext y
    exact (div_eq_mul_inv (-t) y).symm
  have hderivative :
      (-t) * (-(x ^ 2)⁻¹) = t / x ^ 2 := by
    calc
      (-t) * (-(x ^ 2)⁻¹) = t * (x ^ 2)⁻¹ :=
        neg_mul_neg t (x ^ 2)⁻¹
      _ = t / x ^ 2 :=
        (div_eq_mul_inv t (x ^ 2)).symm
  exact
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        HasDerivAt function (t / x ^ 2) x)
      hfunction
      (Eq.subst
        (motive := fun derivative : ℝ =>
          HasDerivAt (fun y : ℝ => (-t) * y⁻¹) derivative x)
        hderivative
        hraw)

/-- Second derivative of the corrected logarithmic Fourier twist on the
positive half-line. -/
theorem Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseFourierTwistedDerivative t m)
      (‖t‖ / x ^ 2)
      x := by
  have hsecond :=
    Complex.logarithmicPhaseRealPhase_deriv_hasDerivAt t hx
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hsecond_norm :
      HasDerivAt
        (fun y : ℝ => -‖t‖ / y)
        (‖t‖ / x ^ 2)
        x := by
    have hfunction :
        (fun y : ℝ => -t / y) =
          (fun y : ℝ => -‖t‖ / y) := by
      funext y
      exact congrArg (fun value : ℝ => -value / y) hnorm.symm
    exact
      Eq.subst
        (motive := fun function : ℝ → ℝ =>
          HasDerivAt function (‖t‖ / x ^ 2) x)
        hfunction
        (Eq.subst
          (motive := fun derivative : ℝ =>
            HasDerivAt (fun y : ℝ => -t / y) derivative x)
          (congrArg (fun value : ℝ => value / x ^ 2) hnorm.symm)
          hsecond)
  have hconstant :
      HasDerivAt
        (fun _y : ℝ => Real.integerAngularFrequency m)
        0
        x :=
    hasDerivAt_const x (Real.integerAngularFrequency m)
  have hsub := hsecond_norm.sub hconstant
  have hfunction :
      (fun y : ℝ => -‖t‖ / y - Real.integerAngularFrequency m) =
        Complex.logarithmicPhaseFourierTwistedDerivative t m := by
    funext y
    rfl
  exact
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        HasDerivAt function (‖t‖ / x ^ 2) x)
      hfunction.symm
      (Eq.subst
        (motive := fun derivative : ℝ =>
          HasDerivAt
            (fun y : ℝ =>
              -‖t‖ / y - Real.integerAngularFrequency m)
            derivative x)
        (sub_zero (‖t‖ / x ^ 2))
        hsub)

/-- First derivative of the corrected logarithmic Fourier twist on the
positive half-line. -/
theorem Complex.logarithmicPhaseFourierTwist_hasDerivAt
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
      (Complex.logarithmicPhaseFourierTwistedDerivative t m x)
      x := by
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx
  have htwist :=
    Complex.hasDerivAt_realPhaseFrequencyTwist m hphase
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hderivative :
      -t / x - Real.integerAngularFrequency m =
        Complex.logarithmicPhaseFourierTwistedDerivative t m x := by
    exact
      congrArg (fun value : ℝ => -value / x - Real.integerAngularFrequency m)
        hnorm.symm
  exact
    Eq.subst
      (motive := fun derivative : ℝ =>
        HasDerivAt
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m)
          derivative x)
      hderivative
      htwist

/-- The corrected logarithmic Fourier derivative denominator is nonzero away
from the unique positive stationary point. -/
theorem Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    {x : ℝ}
    (hx : 0 < x)
    (hstationary :
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x ≠ 0 := by
  have htwisted_ne :
      Complex.logarithmicPhaseFourierTwistedDerivative t m x ≠ 0 := by
    match lt_or_ge m 0 with
    | Or.inl hm =>
        intro hzero
        have hμ : 0 < 2 * Real.pi * (-(m : ℝ)) :=
          Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
        have hx_ne : x ≠ 0 := ne_of_gt hx
        have hreciprocal : ‖t‖ / x = 2 * Real.pi * (-(m : ℝ)) := by
          have hzero_rearranged :
              -‖t‖ / x = 2 * Real.pi * (m : ℝ) :=
            sub_eq_zero.mp hzero
          have hnegated := congrArg Neg.neg hzero_rearranged
          calc
            ‖t‖ / x = -(-‖t‖ / x) := by
              exact
                (neg_neg (‖t‖ / x)).symm.trans
                  (congrArg Neg.neg (neg_div x ‖t‖).symm)
            _ = -(2 * Real.pi * (m : ℝ)) := hnegated
            _ = 2 * Real.pi * (-(m : ℝ)) :=
              (mul_neg (2 * Real.pi) (m : ℝ)).symm
        have hproduct :
            ‖t‖ = (2 * Real.pi * (-(m : ℝ))) * x :=
          (div_eq_iff hx_ne).mp hreciprocal
        have hx_formula :
            x = ‖t‖ / (2 * Real.pi * (-(m : ℝ))) := by
          exact
            (eq_div_iff (ne_of_gt hμ)).mpr
              ((mul_comm x (2 * Real.pi * (-(m : ℝ)))).trans
                hproduct.symm)
        exact hstationary hx_formula
    | Or.inr hm_nonneg =>
        have hT : 0 < ‖t‖ :=
          lt_of_lt_of_le zero_lt_one ht
        have hrecip : 0 < ‖t‖ / x :=
          div_pos hT hx
        have hangular_nonneg :
            0 ≤ Real.integerAngularFrequency m := by
          exact mul_nonneg
            (le_of_lt (mul_pos zero_lt_two Real.pi_pos))
            (Int.cast_nonneg.mpr hm_nonneg)
        have htwisted_neg :
            Complex.logarithmicPhaseFourierTwistedDerivative t m x < 0 := by
          have hnegative : -‖t‖ / x < 0 := by
            exact
              Eq.subst
                (motive := fun value : ℝ => value < 0)
                (neg_div x ‖t‖).symm
                (neg_lt_zero.mpr hrecip)
          exact
            sub_neg_of_lt
              (lt_of_lt_of_le hnegative
                hangular_nonneg)
        exact ne_of_lt htwisted_neg
  exact
    mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr htwisted_ne)

/-- Canonical reciprocal-coefficient derivative for a corrected logarithmic
Fourier twist. -/
def Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
    (t : ℝ)
    (m : ℤ)
    (x : ℝ) : ℂ :=
  -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
    (Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2

theorem Complex.ofReal_logarithmicPhase_velocity_div_sq (t x : ℝ) :
    ((‖t‖ / x ^ 2 : ℝ) : ℂ) = (‖t‖ : ℂ) / (x : ℂ) ^ 2 := by
  exact
    (Complex.ofReal_div ‖t‖ (x ^ 2)).trans
      (congrArg (fun z : ℂ => (‖t‖ : ℂ) / z)
        (Complex.ofReal_pow x 2))

/-- Reciprocal-coefficient derivative for a corrected logarithmic Fourier
twist away from its stationary point. -/
theorem Complex.hasDerivAt_logarithmicPhaseFourierIntegrationCoefficient
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    {x : ℝ}
    (hx : 0 < x)
    (hstationary :
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m))
      (Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x)
      x := by
  change
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m))
      (-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
        (Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
      x
  have hsecond :
      HasDerivAt
        (Complex.logarithmicPhaseFourierTwistedDerivative t m)
        (‖t‖ / x ^ 2)
        x :=
    Complex.logarithmicPhaseFourierTwistedDerivative_hasDerivAt
      t ht_nonneg m hx
  have hdenominator :
      Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x ≠ 0 :=
    Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
      t ht ht_nonneg m hx hstationary
  have hcoefficient :=
    Complex.hasDerivAt_realPhaseIntegrationCoefficient
      (φ' := Complex.logarithmicPhaseFourierTwistedDerivative t m)
      (φ'' := fun y : ℝ => ‖t‖ / y ^ 2)
      hsecond hdenominator
  have htransport :
      (-(Complex.I * ((‖t‖ / x ^ 2 : ℝ) : ℂ)) /
        (Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2) =
        (-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2) :=
    congrArg
      (fun value : ℂ =>
        -(Complex.I * value) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
      (Complex.ofReal_logarithmicPhase_velocity_div_sq t x)
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient
            (Complex.logarithmicPhaseFourierTwistedDerivative t m))
          value x)
      htransport hcoefficient

/-- Exact norm forms for the corrected logarithmic derivative gap and its
reciprocal coefficient. -/
theorem Complex.norm_logarithmicPhaseFourierDerivativeDenominator
    (t : ℝ)
    (m : ℤ)
    (x : ℝ) :
    ‖Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ =
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ := by
  exact
    Complex.norm_realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficient
    (t : ℝ)
    (m : ℤ)
    (x : ℝ) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ =
      ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖⁻¹ := by
  exact
    Complex.norm_realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseFourierTwistedDerivative t m) x

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_eq_frequencyGap
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ =
      ‖(2 * Real.pi * (-(m : ℝ))) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x‖⁻¹ := by
  have hnorm := Complex.norm_logarithmicPhaseFourierIntegrationCoefficient t m x
  have hgap :=
    Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
      t hm hx
  exact
    hnorm.trans
      (congrArg (fun value : ℝ => ‖value‖⁻¹) hgap)

theorem Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    |Complex.logarithmicPhaseFourierTwistedDerivative t m x| =
      |(2 * Real.pi * (-(m : ℝ))) *
        (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x| := by
  exact
    congrArg abs
      (Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
        t hm hx)

theorem Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    |Complex.logarithmicPhaseFourierTwistedDerivative t m x| =
      (2 * Real.pi * (-(m : ℝ))) *
        |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x := by
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hq_abs :
      |2 * Real.pi * (-(m : ℝ))| = 2 * Real.pi * (-(m : ℝ)) :=
    abs_of_pos hq_pos
  have hx_abs : |x| = x := abs_of_pos hx
  have habs :
      |(2 * Real.pi * (-(m : ℝ))) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m) / x| =
        (2 * Real.pi * (-(m : ℝ))) *
          |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x := by
    calc
      _ = |(2 * Real.pi * (-(m : ℝ))) *
          (x - Complex.logarithmicPhaseFourierStationaryPoint t m)| / |x| :=
        abs_div _ _
      _ = |2 * Real.pi * (-(m : ℝ))| *
          |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / |x| := by
        exact congrArg (fun value : ℝ => value / |x|) (abs_mul _ _)
      _ = (2 * Real.pi * (-(m : ℝ))) *
          |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x := by
        exact
          congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
            (congrArg (fun value : ℝ => value *
              |x - Complex.logarithmicPhaseFourierStationaryPoint t m|) hq_abs)
            hx_abs
  exact
    (Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap
      t hm hx).trans habs

theorem Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_left_endpoint_gap
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m ≤ left)
    (hx : x ∈ Set.Icc left right) :
    (2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right ≤
      |Complex.logarithmicPhaseFourierTwistedDerivative t m x| := by
  have hq_nonneg : 0 ≤ 2 * Real.pi * (-(m : ℝ)) :=
    le_of_lt (Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm)
  have hquotient :=
    Complex.frequencyGap_div_right_le_frequencyGap_div_point_of_left_separation
      hq_nonneg hcenter hleft hright hx
  have hderivative :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm (lt_of_lt_of_le hleft hx.1)
  exact hquotient.trans_eq hderivative.symm

theorem Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_right_endpoint_gap
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : right ≤ Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hx : x ∈ Set.Icc left right) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right ≤
      |Complex.logarithmicPhaseFourierTwistedDerivative t m x| := by
  have hq_nonneg : 0 ≤ 2 * Real.pi * (-(m : ℝ)) :=
    le_of_lt (Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm)
  have hquotient :=
    Complex.frequencyGap_div_right_le_frequencyGap_div_point_of_right_separation
      hq_nonneg hcenter hleft hright hx
  have hderivative :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm (lt_of_lt_of_le hleft hx.1)
  have hderivative_right :
      (2 * Real.pi * (-(m : ℝ))) *
          |Complex.logarithmicPhaseFourierStationaryPoint t m - x| / x =
        |Complex.logarithmicPhaseFourierTwistedDerivative t m x| := by
    calc
      _ = (2 * Real.pi * (-(m : ℝ))) *
          |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x :=
        congrArg
          (fun value : ℝ => (2 * Real.pi * (-(m : ℝ))) * value / x)
          (abs_sub_comm _ _)
      _ = |Complex.logarithmicPhaseFourierTwistedDerivative t m x| :=
        hderivative.symm
  exact hquotient.trans_eq hderivative_right

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_left_endpoint_gap_inv
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hx : x ∈ Set.Icc left right) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ ≤
      ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right)⁻¹ := by
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hgap_pos :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right := by
    exact div_pos (mul_pos hq_pos (sub_pos.mpr hcenter)) hright_pos
  have hderivative_lower :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_left_endpoint_gap
      hm hleft hright (le_of_lt hcenter) hx
  have hinverse := inv_anti₀ hgap_pos hderivative_lower
  exact
    (Complex.norm_logarithmicPhaseFourierIntegrationCoefficient t m x).trans_le
      hinverse

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_le_right_endpoint_gap_inv
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m > right)
    (hx : x ∈ Set.Icc left right) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ ≤
      ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right)⁻¹ := by
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hgap_pos :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right := by
    exact div_pos (mul_pos hq_pos (sub_pos.mpr hcenter)) hright_pos
  have hderivative_lower :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_right_endpoint_gap
      hm hleft hright (le_of_lt hcenter) hx
  have hinverse := inv_anti₀ hgap_pos hderivative_lower
  exact
    (Complex.norm_logarithmicPhaseFourierIntegrationCoefficient t m x).trans_le
      hinverse

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficient_eq_positiveFrequencyGap
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ =
      ((2 * Real.pi * (-(m : ℝ))) *
        |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x)⁻¹ := by
  have hnorm :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient t m x
  have hgap :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm hx
  exact hnorm.trans (congrArg Inv.inv hgap)

/-- Exact real norm of the logarithmic reciprocal-coefficient derivative. -/
theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative
    (t : ℝ)
    (m : ℤ)
    (x : ℝ) :
    ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ =
      (‖t‖ / x ^ 2) /
        ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ ^ 2 := by
  unfold Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative
  have hvelocity_nonneg : 0 ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg x)
  have hvelocity_abs : |‖t‖ / x ^ 2| = ‖t‖ / x ^ 2 :=
    abs_of_nonneg hvelocity_nonneg
  have hgeneric :
      ‖-(Complex.I * ((‖t‖ / x ^ 2 : ℝ) : ℂ)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ =
        |‖t‖ / x ^ 2| /
          ‖Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ ^ 2 :=
    Complex.norm_neg_I_mul_real_div_sq
      (‖t‖ / x ^ 2)
      (Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseFourierTwistedDerivative t m) x)
  have hdenominator_norm :
      ‖Complex.realPhaseDerivativeDenominator
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) x‖ =
        ‖Complex.logarithmicPhaseFourierTwistedDerivative t m x‖ :=
    Complex.norm_logarithmicPhaseFourierDerivativeDenominator t m x
  have hvelocity_complex :
      ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ =
        ‖-(Complex.I * ((‖t‖ / x ^ 2 : ℝ) : ℂ)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ :=
    congrArg
      norm
      (congrArg
        (fun value : ℂ =>
          -(Complex.I * value) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
        (Complex.ofReal_logarithmicPhase_velocity_div_sq t x).symm)
  exact
    hvelocity_complex.trans
      (hgeneric.trans
        (congrArg₂ (fun numerator divisor : ℝ => numerator / divisor)
          hvelocity_abs
          (congrArg (fun value : ℝ => value ^ 2) hdenominator_norm)))

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_eq_positiveFrequencyGap
    (t : ℝ)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ =
      (‖t‖ / x ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          |x - Complex.logarithmicPhaseFourierStationaryPoint t m| / x) ^ 2 := by
  have hnorm :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative t m x
  have hgap :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_eq_positiveFrequencyGap
      t hm hx
  exact
    hnorm.trans
      (congrArg
        (fun value : ℝ => (‖t‖ / x ^ 2) / value ^ 2)
        hgap)

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_left_endpoint_gap
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hx : x ∈ Set.Icc left right) :
    ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2 := by
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hderivative_lower :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_left_endpoint_gap
      hm hleft hright (le_of_lt hcenter) hx
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hgap_pos :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right := by
    exact div_pos (mul_pos hq_pos (sub_pos.mpr hcenter)) hright_pos
  have hdenominator_bound :=
    Complex.nonnegative_div_sq_le_of_le
      (div_nonneg (norm_nonneg t) (sq_nonneg x)) hgap_pos hderivative_lower
  have hvelocity_bound : ‖t‖ / x ^ 2 ≤ ‖t‖ / left ^ 2 :=
    Complex.nonnegative_div_sq_le_of_le (norm_nonneg t) hleft hx.1
  have hgap_sq_pos : 0 <
      ((2 * Real.pi * (-(m : ℝ))) *
        (left - Complex.logarithmicPhaseFourierStationaryPoint t m) / right) ^ 2 :=
    sq_pos_of_pos hgap_pos
  have hnumerator_bound :=
    div_le_div_of_nonneg_right hvelocity_bound (le_of_lt hgap_sq_pos)
  have hformula :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative t m x
  exact hformula.trans_le (hdenominator_bound.trans hnumerator_bound)

theorem Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative_le_right_endpoint_gap
    {t : ℝ} {m : ℤ} (hm : m < 0)
    {left right x : ℝ} (hleft : 0 < left) (hright : left ≤ right)
    (hcenter : right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hx : x ∈ Set.Icc left right) :
    ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m x‖ ≤
      (‖t‖ / left ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2 := by
  have hright_pos : 0 < right := lt_of_lt_of_le hleft hright
  have hderivative_lower :=
    Complex.abs_logarithmicPhaseFourierTwistedDerivative_ge_right_endpoint_gap
      hm hleft hright (le_of_lt hcenter) hx
  have hq_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hgap_pos :
      0 < (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right := by
    exact div_pos (mul_pos hq_pos (sub_pos.mpr hcenter)) hright_pos
  have hdenominator_bound :=
    Complex.nonnegative_div_sq_le_of_le
      (div_nonneg (norm_nonneg t) (sq_nonneg x)) hgap_pos hderivative_lower
  have hvelocity_bound : ‖t‖ / x ^ 2 ≤ ‖t‖ / left ^ 2 :=
    Complex.nonnegative_div_sq_le_of_le (norm_nonneg t) hleft hx.1
  have hgap_sq_pos : 0 <
      ((2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - right) / right) ^ 2 :=
    sq_pos_of_pos hgap_pos
  have hnumerator_bound :=
    div_le_div_of_nonneg_right hvelocity_bound (le_of_lt hgap_sq_pos)
  have hformula :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative t m x
  exact hformula.trans_le (hdenominator_bound.trans hnumerator_bound)

/-- Corrected logarithmic Fourier endpoint-tail estimate.  The interval is
assumed to avoid the actual `2πm` stationary point; the two integrability
conditions are the analytic hypotheses discharged by the interval owner. -/
theorem Complex.norm_intervalIntegral_logarithmicPhaseFourierOscillation_le_nonstationary_tail
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (m : ℤ)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hstationary :
      ∀ x ∈ [[left, right]],
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hcoefficientDerivative_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
        volume left right)
    (hoscillationDerivative_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m) x *
            Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x)
        volume left right) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2‖ := by
  let φ : ℝ → ℝ :=
    Complex.realPhaseFrequencyTwist
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m
  let φ' : ℝ → ℝ :=
    Complex.logarithmicPhaseFourierTwistedDerivative t m
  let coefficientDerivative : ℝ → ℂ :=
    fun x =>
      -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
        (Complex.realPhaseDerivativeDenominator φ' x) ^ 2
  let oscillationDerivative : ℝ → ℂ :=
    fun x =>
      Complex.realPhaseOscillation φ x *
        Complex.realPhaseDerivativeDenominator φ' x
  have hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x)
          x := by
    intro x hx
    have hinterval : [[left, right]] = Set.Icc left right :=
      Set.uIcc_of_le hleft_right
    have hx_Icc : x ∈ Set.Icc left right :=
      hinterval ▸ hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le hleft hx_Icc.1
    change
      HasDerivAt
        (Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t m))
        (-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator
            (Complex.logarithmicPhaseFourierTwistedDerivative t m) x) ^ 2)
        x
    exact
      Complex.hasDerivAt_logarithmicPhaseFourierIntegrationCoefficient
        t ht ht_nonneg m hx_pos (hstationary x hx)
  have hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x)
          x := by
    intro x hx
    have hinterval : [[left, right]] = Set.Icc left right :=
      Set.uIcc_of_le hleft_right
    have hx_Icc : x ∈ Set.Icc left right :=
      hinterval ▸ hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le hleft hx_Icc.1
    have htwist :=
      Complex.logarithmicPhaseFourierTwist_hasDerivAt
        t ht_nonneg m hx_pos
    exact Complex.hasDerivAt_realPhaseOscillation htwist
  have hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0 := by
    intro x hx
    have hinterval : [[left, right]] = Set.Icc left right :=
      Set.uIcc_of_le hleft_right
    have hx_Icc : x ∈ Set.Icc left right :=
      hinterval ▸ hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le hleft hx_Icc.1
    exact
      Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
        t ht ht_nonneg m hx_pos (hstationary x hx)
  have hcoefficient_eq :
      (fun x : ℝ =>
        -(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
          (Complex.realPhaseDerivativeDenominator φ' x) ^ 2) =
        coefficientDerivative := by
    funext x
    rfl
  have hoscillation_eq :
      (fun x : ℝ =>
        Complex.realPhaseOscillation φ x *
          Complex.realPhaseDerivativeDenominator φ' x) =
        oscillationDerivative := by
    funext x
    rfl
  have hcoefficient_integrable' :
      IntervalIntegrable coefficientDerivative volume left right := by
    exact hcoefficient_eq.symm ▸ hcoefficientDerivative_integrable
  have hoscillation_integrable' :
      IntervalIntegrable oscillationDerivative volume left right := by
    exact hoscillation_eq.symm ▸ hoscillationDerivative_integrable
  have hbound :=
    Complex.norm_intervalIntegral_realPhaseOscillation_le_boundary_add_remainder
      φ φ' coefficientDerivative oscillationDerivative left right hleft_right
      hcoefficient hoscillation hcoefficient_integrable'
      hoscillation_integrable'
      (fun x _hx => rfl)
      hdenominator
  exact hbound

/-- The corrected stationary point solves the frequency-twist stationary
equation. -/
theorem Complex.logarithmicPhaseRealPhase_fourierStationaryPoint_is_stationary
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {m : ℤ}
    (hm : m < 0) :
    HasDerivAt
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
      0
      (Complex.logarithmicPhaseFourierStationaryPoint t m) := by
  have hphase :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t
      (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm)
  have heq :=
    Complex.logarithmicPhaseRealPhase_deriv_fourierStationaryPoint_eq
      t ht ht_nonneg hm
  have hphase_derivative :
      -t / Complex.logarithmicPhaseFourierStationaryPoint t m =
        Real.integerAngularFrequency m :=
    hphase.deriv.symm.trans heq
  exact
    Complex.realPhaseFrequencyTwist_derivative_eq_zero_of_eq_angularFrequency
      m hphase hphase_derivative

/-- Every corrected active Fourier mode carries its canonical stationary point
and the frequency twist has zero derivative there. -/
theorem Complex.logarithmicPhaseFourierActiveModes_is_stationary
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFourierActiveModes t a b) :
    HasDerivAt
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m)
      0
      (Complex.logarithmicPhaseFourierStationaryPoint t m) := by
  have hm_data :=
    (Complex.mem_logarithmicPhaseFourierActiveModes_iff t a b m).mp hm
  exact
    Complex.logarithmicPhaseRealPhase_fourierStationaryPoint_is_stationary
      t ht ht_nonneg hm_data.2.1

/-- A positive point at which the logarithmic Fourier twist has zero
derivative is necessarily its corrected stationary point. -/
theorem Complex.logarithmicPhaseFourierTwistedDerivative_eq_zero_iff_stationaryPoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℤ}
    (hm : m < 0)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseFourierTwistedDerivative t m x = 0 ↔
      x = Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hμ_pos : 0 < 2 * Real.pi * (-(m : ℝ)) :=
    Complex.logarithmicPhaseFourierStationaryPoint_denominator_pos m hm
  have hμ_ne : 2 * Real.pi * (-(m : ℝ)) ≠ 0 :=
    ne_of_gt hμ_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx
  constructor
  · intro hzero
    have hreciprocal : ‖t‖ / x = 2 * Real.pi * (-(m : ℝ)) := by
      have hzero_rearranged :
          -‖t‖ / x = 2 * Real.pi * (m : ℝ) := by
        exact sub_eq_zero.mp hzero
      have hnegated := congrArg Neg.neg hzero_rearranged
      calc
        ‖t‖ / x = -(-‖t‖ / x) := by
          exact
            (neg_neg (‖t‖ / x)).symm.trans
              (congrArg Neg.neg (neg_div x ‖t‖).symm)
        _ = -(2 * Real.pi * (m : ℝ)) := hnegated
        _ = 2 * Real.pi * (-(m : ℝ)) :=
          (mul_neg (2 * Real.pi) (m : ℝ)).symm
    have hproduct :
        ‖t‖ = (2 * Real.pi * (-(m : ℝ))) * x :=
      (div_eq_iff hx_ne).mp hreciprocal
    have hx_formula :
        x = ‖t‖ / (2 * Real.pi * (-(m : ℝ))) := by
      exact
        (eq_div_iff hμ_ne).mpr
          ((mul_comm x (2 * Real.pi * (-(m : ℝ)))).trans
            hproduct.symm)
    exact hx_formula
  · intro hx_stationary
    have hreciprocal :
        ‖t‖ / x = 2 * Real.pi * (-(m : ℝ)) := by
      have hidentity :=
        Real.logarithmicPhase_fourier_reciprocal_identity
          hT_pos hμ_pos
      exact
        Eq.subst
          (motive := fun value : ℝ => ‖t‖ / value =
            2 * Real.pi * (-(m : ℝ)))
          hx_stationary.symm
          hidentity
    have hnegative :
        -‖t‖ / x = 2 * Real.pi * (m : ℝ) := by
      calc
        -‖t‖ / x = -(‖t‖ / x) := neg_div x ‖t‖
        _ = -(2 * Real.pi * (-(m : ℝ))) :=
          congrArg Neg.neg hreciprocal
        _ = 2 * Real.pi * (m : ℝ) := by
          calc
            -(2 * Real.pi * (-(m : ℝ))) =
                (2 * Real.pi) * (-(-(m : ℝ))) :=
              (mul_neg (2 * Real.pi) (-(m : ℝ))).symm
            _ = 2 * Real.pi * (m : ℝ) := by
              exact congrArg (fun value : ℝ => (2 * Real.pi) * value)
                (neg_neg (m : ℝ))
    exact sub_eq_zero.mpr hnegative

end

end LFunctions
end Boundary
