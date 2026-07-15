import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.MonotoneStationaryTailVariation

/-!
# Sharp one-sided logarithmic stationary tails

The two public theorems in this file consume the generic monotone
reciprocal-derivative estimate.  Every analytic hypothesis is discharged from
the corrected logarithmic Fourier formulas.  The resulting bounds depend only
on the reciprocal derivative at the edge nearest the stationary point; no
interval-length times curvature remainder survives.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

/-- The logarithmic Fourier center is excluded from an interval lying strictly
to its left. -/
theorem Complex.logarithmicPhase_stationaryPoint_ne_on_left_interval
    (t : ℝ) (m : ℤ) {left right : ℝ}
    (hleft_right : left ≤ right)
    (hcenter :
      right < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ∀ x ∈ Set.Icc left right,
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
  intro x hx
  exact
    Complex.logarithmicPhaseFourierStationaryPoint_ne_of_lt t
      (lt_of_le_of_lt hx.2 hcenter)

/-- The logarithmic Fourier center is excluded from an interval lying strictly
to its right. -/
theorem Complex.logarithmicPhase_stationaryPoint_ne_on_right_interval
    (t : ℝ) (m : ℤ) {left right : ℝ}
    (hleft_right : left ≤ right)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < left) :
    ∀ x ∈ Set.Icc left right,
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
  intro x hx
  exact
    Complex.logarithmicPhaseFourierStationaryPoint_ne_of_gt t
      (lt_of_lt_of_le hcenter hx.1)

/-- Transfer center exclusion from `Icc` to the unoriented interval. -/
theorem Complex.logarithmicPhase_stationaryPoint_ne_on_uIcc_of_Icc
    (t : ℝ) (m : ℤ) {left right : ℝ}
    (hleft_right : left ≤ right)
    (hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ∀ x ∈ [[left, right]],
      x ≠ Complex.logarithmicPhaseFourierStationaryPoint t m := by
  intro x hx
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hxIcc : x ∈ Set.Icc left right :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
  exact hstationary x hxIcc

/-- Every point of a positive ordered interval is positive. -/
theorem Real.pos_of_mem_uIcc_of_pos_left
    {left right x : ℝ}
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hx : x ∈ [[left, right]]) :
    0 < x := by
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hxIcc : x ∈ Set.Icc left right :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
  exact lt_of_lt_of_le hleft hxIcc.1

/-- Every point of a left stationary tail remains left of the center. -/
theorem Complex.lt_stationaryPoint_of_mem_left_uIcc
    (t : ℝ) (m : ℤ) {left right x : ℝ}
    (hleft_right : left ≤ right)
    (hcenter :
      right < Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hx : x ∈ [[left, right]]) :
    x < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hxIcc : x ∈ Set.Icc left right :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
  exact lt_of_le_of_lt hxIcc.2 hcenter

/-- Every point of a right stationary tail remains right of the center. -/
theorem Complex.stationaryPoint_lt_of_mem_right_uIcc
    (t : ℝ) (m : ℤ) {left right x : ℝ}
    (hleft_right : left ≤ right)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < left)
    (hx : x ∈ [[left, right]]) :
    Complex.logarithmicPhaseFourierStationaryPoint t m < x := by
  have huIcc : [[left, right]] = Set.Icc left right :=
    Set.uIcc_of_le hleft_right
  have hxIcc : x ∈ Set.Icc left right :=
    Eq.subst (motive := fun s : Set ℝ => x ∈ s) huIcc hx
  exact lt_of_lt_of_le hcenter hxIcc.1

/-- Sharp logarithmic nonstationary estimate on the interval left of a
stationary point. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) (hm : m < 0)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hcenter :
      right < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseLeftReciprocalGap t m right +
        Complex.logarithmicPhaseLeftReciprocalGap t m right := by
  let φ : ℝ → ℝ :=
    Complex.realPhaseFrequencyTwist
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m
  let φ' : ℝ → ℝ :=
    Complex.logarithmicPhaseFourierTwistedDerivative t m
  let coefficientDerivative : ℝ → ℂ :=
    Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m
  let oscillationDerivative : ℝ → ℂ := fun x =>
    Complex.realPhaseOscillation φ x *
      Complex.realPhaseDerivativeDenominator φ' x
  let q : ℝ → ℝ :=
    Complex.logarithmicPhaseLeftReciprocalGap t m
  let q' : ℝ → ℝ :=
    Complex.logarithmicPhaseLeftReciprocalGapDerivative t m
  have hstationaryIcc :=
    Complex.logarithmicPhase_stationaryPoint_ne_on_left_interval
      t m hleft_right hcenter
  have hstationaryUIcc :=
    Complex.logarithmicPhase_stationaryPoint_ne_on_uIcc_of_Icc
      t m hleft_right hstationaryIcc
  have hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    exact
      Complex.hasDerivAt_logarithmicPhaseFourierIntegrationCoefficient
        t ht ht_nonneg m hxPos (hstationaryUIcc x hx)
  have hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    have htwist :=
      Complex.logarithmicPhaseFourierTwist_hasDerivAt
        t ht_nonneg m hxPos
    exact Complex.hasDerivAt_realPhaseOscillation htwist
  have hcoefficientIntegrable :
      IntervalIntegrable coefficientDerivative volume left right :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationaryIcc
  have hoscillationIntegrable :
      IntervalIntegrable oscillationDerivative volume left right :=
    Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
      t ht_nonneg m left right hleft hleft_right
  have hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0 := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    exact
      Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
        t ht ht_nonneg m hxPos (hstationaryUIcc x hx)
  have hqLeft :
      q left =
        ‖Complex.realPhaseIntegrationCoefficient φ' left‖ := by
    exact
      Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
        t ht m hm hleft
        (lt_of_le_of_lt hleft_right hcenter)
  have hrightPos : 0 < right :=
    lt_of_lt_of_le hleft hleft_right
  have hqRight :
      q right =
        ‖Complex.realPhaseIntegrationCoefficient φ' right‖ := by
    exact
      Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
        t ht m hm hrightPos hcenter
  have hnormDerivative :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x| := by
    intro x _
    exact
      (Complex.abs_logarithmicPhaseLeftReciprocalGapDerivative_eq_coefficientDerivativeNorm
        t m x).symm
  have hqDeriv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    have hxCenter :=
      Complex.lt_stationaryPoint_of_mem_left_uIcc
        t m hleft_right hcenter hx
    exact
      Complex.hasDerivAt_logarithmicPhaseLeftReciprocalGap
        t ht ht_nonneg m hxPos hxCenter
  have hqIntegrable :
      IntervalIntegrable q' volume left right :=
    Complex.intervalIntegrable_logarithmicPhaseLeftReciprocalGapDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationaryIcc
  have hqNonneg :
      ∀ x ∈ Set.Icc left right, 0 ≤ q' x := by
    intro x _
    exact
      Complex.logarithmicPhaseLeftReciprocalGapDerivative_nonneg t m x
  exact
    Complex.norm_intervalIntegral_realPhaseOscillation_le_twice_rightCoefficient
      φ φ' coefficientDerivative oscillationDerivative q q'
      left right hleft_right hcoefficient hoscillation
      hcoefficientIntegrable hoscillationIntegrable
      (fun x _ => rfl) hdenominator hqLeft hqRight
      hnormDerivative hqDeriv hqIntegrable hqNonneg

/-- Sharp logarithmic nonstationary estimate on the interval right of a
stationary point. -/
theorem Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (m : ℤ) (hm : m < 0)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < left) :
    ‖∫ x in left..right,
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseRightReciprocalGap t m left +
        Complex.logarithmicPhaseRightReciprocalGap t m left := by
  let φ : ℝ → ℝ :=
    Complex.realPhaseFrequencyTwist
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m
  let φ' : ℝ → ℝ :=
    Complex.logarithmicPhaseFourierTwistedDerivative t m
  let coefficientDerivative : ℝ → ℂ :=
    Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t m
  let oscillationDerivative : ℝ → ℂ := fun x =>
    Complex.realPhaseOscillation φ x *
      Complex.realPhaseDerivativeDenominator φ' x
  let q : ℝ → ℝ :=
    Complex.logarithmicPhaseRightReciprocalGap t m
  let q' : ℝ → ℝ :=
    Complex.logarithmicPhaseRightReciprocalGapDerivative t m
  have hstationaryIcc :=
    Complex.logarithmicPhase_stationaryPoint_ne_on_right_interval
      t m hleft_right hcenter
  have hstationaryUIcc :=
    Complex.logarithmicPhase_stationaryPoint_ne_on_uIcc_of_Icc
      t m hleft_right hstationaryIcc
  have hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseIntegrationCoefficient φ')
          (coefficientDerivative x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    exact
      Complex.hasDerivAt_logarithmicPhaseFourierIntegrationCoefficient
        t ht ht_nonneg m hxPos (hstationaryUIcc x hx)
  have hoscillation :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.realPhaseOscillation φ)
          (oscillationDerivative x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    have htwist :=
      Complex.logarithmicPhaseFourierTwist_hasDerivAt
        t ht_nonneg m hxPos
    exact Complex.hasDerivAt_realPhaseOscillation htwist
  have hcoefficientIntegrable :
      IntervalIntegrable coefficientDerivative volume left right :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationaryIcc
  have hoscillationIntegrable :
      IntervalIntegrable oscillationDerivative volume left right :=
    Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
      t ht_nonneg m left right hleft hleft_right
  have hdenominator :
      ∀ x ∈ [[left, right]],
        Complex.realPhaseDerivativeDenominator φ' x ≠ 0 := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    exact
      Complex.logarithmicPhaseFourierDerivativeDenominator_ne_zero
        t ht ht_nonneg m hxPos (hstationaryUIcc x hx)
  have hqLeft :
      q left =
        ‖Complex.realPhaseIntegrationCoefficient φ' left‖ := by
    exact
      Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
        t ht m hm hleft hcenter
  have hrightPos : 0 < right :=
    lt_of_lt_of_le hleft hleft_right
  have hrightCenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < right :=
    lt_of_lt_of_le hcenter hleft_right
  have hqRight :
      q right =
        ‖Complex.realPhaseIntegrationCoefficient φ' right‖ := by
    exact
      Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
        t ht m hm hrightPos hrightCenter
  have hnormDerivative :
      ∀ x ∈ [[left, right]],
        ‖coefficientDerivative x‖ = |q' x| := by
    intro x _
    exact
      (Complex.abs_logarithmicPhaseRightReciprocalGapDerivative_eq_coefficientDerivativeNorm
        t m x).symm
  have hqDeriv :
      ∀ x ∈ [[left, right]], HasDerivAt q (q' x) x := by
    intro x hx
    have hxPos :=
      Real.pos_of_mem_uIcc_of_pos_left hleft hleft_right hx
    have hxCenter :=
      Complex.stationaryPoint_lt_of_mem_right_uIcc
        t m hleft_right hcenter hx
    exact
      Complex.hasDerivAt_logarithmicPhaseRightReciprocalGap
        t ht ht_nonneg m hxPos hxCenter
  have hqIntegrable :
      IntervalIntegrable q' volume left right :=
    Complex.intervalIntegrable_logarithmicPhaseRightReciprocalGapDerivative
      t ht ht_nonneg m left right hleft hleft_right hstationaryIcc
  have hqNonpos :
      ∀ x ∈ Set.Icc left right, q' x ≤ 0 := by
    intro x _
    exact
      Complex.logarithmicPhaseRightReciprocalGapDerivative_nonpos t m x
  exact
    Complex.norm_intervalIntegral_realPhaseOscillation_le_twice_leftCoefficient
      φ φ' coefficientDerivative oscillationDerivative q q'
      left right hleft_right hcoefficient hoscillation
      hcoefficientIntegrable hoscillationIntegrable
      (fun x _ => rfl) hdenominator hqLeft hqRight
      hnormDerivative hqDeriv hqIntegrable hqNonpos

end

end LFunctions
end Boundary
