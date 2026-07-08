import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseClosedBranch
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongActiveWeyl

/-!
# Real-phase positive long branch

This file owns the positive long-branch wrapper after the four packet
contribution budgets have been proved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Positive long-branch real-phase estimate from closed stationary and
endpoint packet-contribution budgets. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationary_endpoint_budgets
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hendpoint :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        60 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hstationary hendpoint

/-- Positive long-branch real-phase estimate from the stationary and endpoint
tail packet budgets. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_tail_budgets
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfar :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_tail_budgets
      t ht ht_nonneg ha hab hstationary hleft hfar

/-- Positive long-branch real-phase estimate from the stationary budget and
endpoint reciprocal-scale cut cardinality bounds. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaleCut_bounds
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleftScale :
      (((Finset.Icc a b).filter
        (fun n : ℕ => ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ))).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfarScale :
      (((Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (n : ℝ) < ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_scaleCut_bounds
      t ht ht_nonneg ha hab hstationary hleftScale hfarScale

/-- Positive long-branch real-phase estimate from stationary sample-union
control and endpoint reciprocal-scale cut cardinality bounds. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamily_scaleCut_bounds
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary_family :
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleftScale :
      (((Finset.Icc a b).filter
        (fun n : ℕ => ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ))).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfarScale :
      (((Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (n : ℝ) < ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_twentyTarget_of_familyUnion_ten
      t ht hstationary_family
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaleCut_bounds
      t ht_nonneg ht ha hab _hab_strict _hlong_sqrt _hlong_endpoint
      hstationary hleftScale hfarScale

/-- Positive long-branch real-phase estimate from the explicit Weyl-envelope
radicand target and shifted-increment data. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_weylEnvelope_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt hinc_mono hred_mono hsep hrad

/-- Positive long-branch real-phase estimate from the exact weighted
Weyl-envelope radicand target and shifted-increment data. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_weightedWeylEnvelope_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hrad :
      (Real.secondDerivativeVdc_blockLength a b +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              Real.secondDerivativeVdc_blockLength a b +
                2 *
                  (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                    (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                    (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_radicand_target_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt hinc_mono hred_mono hsep hrad

/-- Positive long-branch real-phase estimate from a direct shifted-increment
`π` bound, direct separated-increment data, and the explicit Weyl-envelope
radicand target.  The reduced-increment monotonicity hypothesis is discharged
from no-winding, so later resonance-partition arguments only need to supply
separation on the selected pieces. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_sep_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi)
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) :=
    fun h _hmem =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
        t ht_nonneg ha
  have hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_reduced_mono_of_gap_pi
      t ht_nonneg ha hgap_pi
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_weylEnvelope_radicand
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      hinc_mono hred_mono hsep hrad

/-- Positive long-branch real-phase estimate from canonical zero-centered
resonance-window decompositions and the enlarged-envelope radicand target. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_canonical_zero_resonanceWindow_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (c d : ℕ → ℕ)
    (M : ℕ → ℝ)
    (hc :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ c h)
    (hcd :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          c h ≤ d h)
    (hdb :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          d h ≤ b - h)
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico (c h) (d h))
    (hlength :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ((d h - c h : ℕ) : ℝ) ≤ M h)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((M h +
                    (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg_of_gap_pi_canonical_zero_resonanceWindow_data
      t ht ht_nonneg ha hab hlong_sqrt c d M hc hcd hdb hgap_pi hwindow
      hlength hrad

/-- Positive long-branch real-phase estimate from the canonical zero-centered
resonance-window construction, a uniform length budget for every constructed
window, and the enlarged-envelope radicand target. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_canonical_zero_resonanceWindow_length_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (M : ℕ → ℝ)
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi)
    (hlength :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (0 : ℝ))
                (‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ)) =
              Finset.Ico c d →
            ((d - c : ℕ) : ℝ) ≤ M h)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((M h +
                    (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength ‖t‖
  have hgap :
      H ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  have habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h :=
    fun h hmem =>
      Nat.realPhase_secondDerivative_vdc_lower_le_sub_shift hgap hmem
  have hexists :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∃ c d : ℕ,
            a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧
              Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (0 : ℝ))
                (‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ)) =
                Finset.Ico c d :=
    fun h hmem =>
      Complex.realPhase_secondDerivative_vdc_logarithmic_resonanceWindow_exists_canonical_of_nonneg
        (t := t)
        (ht_nonneg := ht_nonneg)
        (a := a)
        (b := b)
        (h := h)
        (resonance := 2 * Real.pi * (0 : ℝ))
        (lam :=
          ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ))
        ha (habh h hmem)
  let cfun : ℕ → ℕ :=
    fun h =>
      if hmem : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H then
        Classical.choose (hexists h hmem)
      else
        a
  let dfun : ℕ → ℕ :=
    fun h =>
      if hmem : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H then
        Classical.choose (Classical.choose_spec (hexists h hmem))
      else
        a
  have hc :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ cfun h := by
    intro h hmem
    let c0 : ℕ := Classical.choose (hexists h hmem)
    let d0 : ℕ := Classical.choose (Classical.choose_spec (hexists h hmem))
    have hcd_spec :
        a ≤ c0 ∧ c0 ≤ d0 ∧ d0 ≤ b - h ∧
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico c0 d0 :=
      Classical.choose_spec (Classical.choose_spec (hexists h hmem))
    have hcfun : cfun h = c0 :=
      dif_pos hmem
    exact
      Eq.subst
        (motive := fun x : ℕ => a ≤ x)
        hcfun.symm
        hcd_spec.1
  have hcd :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          cfun h ≤ dfun h := by
    intro h hmem
    let c0 : ℕ := Classical.choose (hexists h hmem)
    let d0 : ℕ := Classical.choose (Classical.choose_spec (hexists h hmem))
    have hcd_spec :
        a ≤ c0 ∧ c0 ≤ d0 ∧ d0 ≤ b - h ∧
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico c0 d0 :=
      Classical.choose_spec (Classical.choose_spec (hexists h hmem))
    have hcfun : cfun h = c0 :=
      dif_pos hmem
    have hdfun : dfun h = d0 :=
      dif_pos hmem
    exact
      Eq.subst
        (motive := fun y : ℕ => cfun h ≤ y)
        hdfun.symm
        (Eq.subst
          (motive := fun x : ℕ => x ≤ d0)
          hcfun.symm
          hcd_spec.2.1)
  have hdb :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          dfun h ≤ b - h := by
    intro h hmem
    let c0 : ℕ := Classical.choose (hexists h hmem)
    let d0 : ℕ := Classical.choose (Classical.choose_spec (hexists h hmem))
    have hcd_spec :
        a ≤ c0 ∧ c0 ≤ d0 ∧ d0 ≤ b - h ∧
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico c0 d0 :=
      Classical.choose_spec (Classical.choose_spec (hexists h hmem))
    have hdfun : dfun h = d0 :=
      dif_pos hmem
    exact
      Eq.subst
        (motive := fun y : ℕ => y ≤ b - h)
        hdfun.symm
        hcd_spec.2.2.1
  have hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico (cfun h) (dfun h) := by
    intro h hmem
    let c0 : ℕ := Classical.choose (hexists h hmem)
    let d0 : ℕ := Classical.choose (Classical.choose_spec (hexists h hmem))
    have hcd_spec :
        a ≤ c0 ∧ c0 ≤ d0 ∧ d0 ≤ b - h ∧
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico c0 d0 :=
      Classical.choose_spec (Classical.choose_spec (hexists h hmem))
    have hcfun : cfun h = c0 :=
      dif_pos hmem
    have hdfun : dfun h = d0 :=
      dif_pos hmem
    exact
      Eq.subst
        (motive := fun y : ℕ =>
          Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) =
            Finset.Ico (cfun h) y)
        hdfun.symm
        (Eq.subst
          (motive := fun x : ℕ =>
            Complex.realPhase_integerIncrementResonanceWindow
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              a (b - h) (2 * Real.pi * (0 : ℝ))
              (‖t‖ *
                ((((b + 1 : ℕ) : ℝ) *
                  (((b + 1 : ℕ) : ℝ)))⁻¹) *
                (h : ℝ)) =
              Finset.Ico x d0)
          hcfun.symm
          hcd_spec.2.2.2)
  have hlength_chosen :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ((dfun h - cfun h : ℕ) : ℝ) ≤ M h :=
    fun h hmem =>
      hlength h hmem (cfun h) (dfun h) (hwindow h hmem)
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_canonical_zero_resonanceWindow_radicand
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint cfun dfun M
      hc hcd hdb hgap_pi hwindow hlength_chosen hrad

/-- Positive long-branch real-phase estimate from the Weyl target, with
reduced-increment monotonicity supplied directly and separation supplied by
all-integer resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (S : ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ m : ℕ,
              m ∈ S h k ↔
                m ∈ Finset.Ico a (b - h) ∧
                  ‖Complex.realPhase_integerIncrement
                      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                        h)
                      m -
                    (2 * Real.pi * (k : ℝ))‖ <
                    (‖t‖ *
                      ((((b + 1 : ℕ) : ℝ) *
                        (((b + 1 : ℕ) : ℝ)))⁻¹) *
                      (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                n ∉ S h k)
    (hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_integer_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt hred_mono S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the explicit Weyl-envelope
radicand target, with reduced-increment monotonicity supplied directly and
separation supplied by all-integer resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_resonanceWindow_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (S : ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ m : ℕ,
              m ∈ S h k ↔
                m ∈ Finset.Ico a (b - h) ∧
                  ‖Complex.realPhase_integerIncrement
                      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                        h)
                      m -
                    (2 * Real.pi * (k : ℝ))‖ <
                    (‖t‖ *
                      ((((b + 1 : ℕ) : ℝ) *
                        (((b + 1 : ℕ) : ℝ)))⁻¹) *
                      (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                n ∉ S h k)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have htarget_nonneg :
      0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg
      hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_resonanceWindow
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      hred_mono S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the Weyl target, with
reduced-increment monotonicity supplied by fixed integer branch strips and
separation supplied by all-integer resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_strip_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (K : ℕ → ℤ)
    (hstrip :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  n -
                  (2 * Real.pi * ((K h : ℤ) : ℝ)) ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (S : ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ m : ℕ,
              m ∈ S h k ↔
                m ∈ Finset.Ico a (b - h) ∧
                  ‖Complex.realPhase_integerIncrement
                      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                        h)
                      m -
                    (2 * Real.pi * (k : ℝ))‖ <
                    (‖t‖ *
                      ((((b + 1 : ℕ) : ℝ) *
                        (((b + 1 : ℕ) : ℝ)))⁻¹) *
                      (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                n ∉ S h k)
    (hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_integer_strip_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt K hstrip S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the explicit Weyl-envelope
radicand target, with reduced-increment monotonicity supplied by fixed integer
branch strips and separation supplied by all-integer resonance-window
avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_strip_resonanceWindow_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (K : ℕ → ℤ)
    (hstrip :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  n -
                  (2 * Real.pi * ((K h : ℤ) : ℝ)) ∈
                Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (S : ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ m : ℕ,
              m ∈ S h k ↔
                m ∈ Finset.Ico a (b - h) ∧
                  ‖Complex.realPhase_integerIncrement
                      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                        h)
                      m -
                    (2 * Real.pi * (k : ℝ))‖ <
                    (‖t‖ *
                      ((((b + 1 : ℕ) : ℝ) *
                        (((b + 1 : ℕ) : ℝ)))⁻¹) *
                      (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                n ∉ S h k)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have htarget_nonneg :
      0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg
      hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_strip_resonanceWindow
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      K hstrip S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the Weyl target, with
no-winding discharged by scaled reciprocal arithmetic and separation supplied
by zero-centered resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hscaled_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                Real.pi)
    (S : ℕ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ m : ℕ,
            m ∈ S h ↔
              m ∈ Finset.Ico a (b - h) ∧
                ‖Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    m -
                  (2 * Real.pi * (0 : ℝ))‖ <
                  (‖t‖ *
                    ((((b + 1 : ℕ) : ℝ) *
                      (((b + 1 : ℕ) : ℝ)))⁻¹) *
                    (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              n ∉ S h)
    (hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_scaled_reciprocal_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt hscaled_pi S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the explicit Weyl-envelope
radicand target, with no-winding discharged by scaled reciprocal arithmetic
and separation supplied by zero-centered resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_resonanceWindow_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hscaled_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                Real.pi)
    (S : ℕ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ m : ℕ,
            m ∈ S h ↔
              m ∈ Finset.Ico a (b - h) ∧
                ‖Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    m -
                  (2 * Real.pi * (0 : ℝ))‖ <
                  (‖t‖ *
                    ((((b + 1 : ℕ) : ℝ) *
                      (((b + 1 : ℕ) : ℝ)))⁻¹) *
                    (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              n ∉ S h)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have htarget_nonneg :
      0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg
      hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_resonanceWindow
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      hscaled_pi S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the Weyl target, with
no-winding supplied directly as a shifted-increment `π` bound and separation
supplied by zero-centered resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi)
    (S : ℕ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ m : ℕ,
            m ∈ S h ↔
              m ∈ Finset.Ico a (b - h) ∧
                ‖Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    m -
                  (2 * Real.pi * (0 : ℝ))‖ <
                  (‖t‖ *
                    ((((b + 1 : ℕ) : ℝ) *
                      (((b + 1 : ℕ) : ℝ)))⁻¹) *
                    (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              n ∉ S h)
    (hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_gap_pi_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt hgap_pi S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the explicit Weyl-envelope
radicand target, with no-winding supplied directly as a shifted-increment `π`
bound and separation supplied by zero-centered resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_resonanceWindow_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi)
    (S : ℕ → Finset ℕ)
    (hS :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ m : ℕ,
            m ∈ S h ↔
              m ∈ Finset.Ico a (b - h) ∧
                ‖Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    m -
                  (2 * Real.pi * (0 : ℝ))‖ <
                  (‖t‖ *
                    ((((b + 1 : ℕ) : ℝ) *
                      (((b + 1 : ℕ) : ℝ)))⁻¹) *
                    (h : ℝ)))
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              n ∉ S h)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have htarget_nonneg :
      0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg
      hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_resonanceWindow
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      hgap_pi S hS havoid hweyl_target

/-- Positive long-branch real-phase estimate from the stationary budget and
closed-subinterval endpoint budgets. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_Icc_endpoint_bounds
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleftIcc :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc a r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfarIcc :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_Icc_endpoint_bounds
      t ht ht_nonneg ha hab hstationary hleftIcc hfarIcc

/-- Positive long-branch real-phase estimate from uniform closed-subinterval
twentieth-budget estimates. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_Icc_bounds
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hIcc :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_Icc_bounds
      t ht ht_nonneg ha hab hIcc

/-- Positive long-branch real-phase estimate from the stationary budget and
explicit first-derivative data on endpoint subintervals. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_endpoint_firstDerivative_data
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft_reduced :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r)
    (hleft_sep :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r
            (‖t‖ / ((r + 1 : ℕ) : ℝ)))
    (hfar_reduced :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r)
    (hfar_sep :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r
            (‖t‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_endpoint_firstDerivative_data
      t ht ht_nonneg ha hab hstationary
      hleft_reduced hleft_sep hfar_reduced hfar_sep

/-- Positive long-branch real-phase estimate from stationary sample-union
control and explicit first-derivative data on endpoint subintervals. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamily_endpoint_firstDerivative_data
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary_family :
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft_reduced :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r)
    (hleft_sep :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r
            (‖t‖ / ((r + 1 : ℕ) : ℝ)))
    (hfar_reduced :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r)
    (hfar_sep :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r
            (‖t‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_stationaryFamily_endpoint_firstDerivative_data
      t ht ht_nonneg ha hab hstationary_family
      hleft_reduced hleft_sep hfar_reduced hfar_sep

/-- Positive long-branch real-phase estimate from twentieth-budget stationary
sample-union control and explicit first-derivative data on endpoint
subintervals. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamilyTwenty_endpoint_firstDerivative_data
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hstationary_family :
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft_reduced :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r)
    (hleft_sep :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a r
            (‖t‖ / ((r + 1 : ℕ) : ℝ)))
    (hfar_reduced :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r)
    (hfar_sep :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            c r
            (‖t‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget_of_stationaryFamilyTwenty_endpoint_firstDerivative_data
      t ht ht_nonneg ha hab hstationary_family
      hleft_reduced hleft_sep hfar_reduced hfar_sep

end

end LFunctions
end Boundary
