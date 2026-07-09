import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseClosedBranch
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongActiveWeyl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongSpanRange
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongActiveWindows
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseZeroResonanceWindowEmpty
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongChordAbel

/-!
# Real-phase positive long branch

This file owns the positive long-branch wrapper after the shifted-correlation
Abel and additive all-integer resonance budgets have been proved.
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

/-- Positive long-branch real-phase estimate from range-counted active
resonance windows and the corresponding explicit Weyl-envelope radicand
target. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_radicand
    (t : ℝ)
    (_ht_nonneg : 0 ≤ t)
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
    {lam W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
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
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    ((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_radicand
      t ht ha hab hlong_sqrt habh hpos hlam hlam_pi hrange hwindow
      hW_nonneg hderiv_antitone hderiv_lower hinc_mono hred_mono hrad

/-- Positive long-branch real-phase estimate from range-counted active
resonance windows and the refined all-principal-branch complement radicand. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
    (t : ℝ)
    (_ht_nonneg : 0 ≤ t)
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
    {lam W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    (((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) *
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
      t ht ha hab hlong_sqrt habh hpos hlam hlam_pi hrange hwindow
      hW_nonneg hinc_mono hrad

/-- Positive long-branch real-phase estimate from range-counted active
resonance windows and the first-derivative all-principal-branch complement
radicand. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
    (t : ℝ)
    (_ht_nonneg : 0 ≤ t)
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
    {eta W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
                    ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (eta h)).card + 1 : ℕ) *
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
                      (4 * ((eta h)⁻¹ + 1) +
                        4 * Real.pi * (eta h)⁻¹))) +
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
      t ht ha hab hlong_sqrt habh heta_pos heta_pi hrange hwindow
      hW_nonneg hinc_mono hrad

/-- Positive long-branch real-phase estimate from first-derivative
all-integer resonance control, with resonant-window lengths discharged by the
monotone endpoint-spread estimate. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_endpoint_spread_refinedPrincipalFirstDerivative_radicand
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
    {eta rho W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          eta h ≤ Real.pi)
    (hrho_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < rho h)
    (hW :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (2 * eta h) / rho h + 1 ≤ W h)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hrational :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ c d : ℕ,
              Complex.realPhase_integerIncrementResonanceWindow
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  a (b - h) (2 * Real.pi * (k : ℝ)) (eta h) =
                Finset.Ico c d →
              c < d - 1 →
                rho h * (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))))
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
                    ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (eta h)).card + 1 : ℕ) *
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (lo h) (hi h) Real.pi).card : ℕ) : ℝ) *
                      (4 * ((eta h)⁻¹ + 1) +
                        4 * Real.pi * (eta h)⁻¹))) +
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
  have heta_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ eta h :=
    fun h hh => le_of_lt (heta_pos h hh)
  have hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
      t ht_nonneg ha habh hinc_mono heta_nonneg hrho_pos hW hrational
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_refinedPrincipalFirstDerivative_radicand
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      habh heta_pos heta_pi hrange hwindow hW_nonneg hinc_mono hrad

/-- Positive long-branch real-phase estimate from range-counted active
resonance windows, with the window-length hypothesis discharged by the
monotone endpoint-spread estimate. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_endpoint_spread_radicand
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
    {lam rho W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hpos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          1 ≤ h)
    (hlam :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h =
            ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          lam h ≤ Real.pi)
    (hlam_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ lam h)
    (hrho_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < rho h)
    (hW :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (2 * lam h) / rho h + 1 ≤ W h)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hrational :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ c d : ℕ,
              Complex.realPhase_integerIncrementResonanceWindow
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  a (b - h) (2 * Real.pi * (k : ℝ)) (lam h) =
                Finset.Ico c d →
              c < d - 1 →
                rho h * (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))))
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
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
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (lam h)).card : ℕ) : ℝ) * W h +
                    ((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (lam h)).card + 1 : ℕ) : ℝ) *
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
  have hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (lam h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                  ℝ) ≤ W h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
      t ht_nonneg ha habh hinc_mono hlam_nonneg hrho_pos hW hrational
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_radicand
      t ht_nonneg ht ha hab _hab_strict hlong_sqrt _hlong_endpoint
      habh hpos hlam hlam_pi hrange hwindow hW_nonneg
      hderiv_antitone hderiv_lower hinc_mono hred_mono hrad

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

/-- Positive long-branch real-phase estimate from the positive-branch empty
zero-centered resonance window and the enlarged-envelope radicand target. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_zero_resonanceWindow_empty_radicand
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
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((0 : ℝ) +
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
  have hlength :
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
            ((d - c : ℕ) : ℝ) ≤ (fun _ : ℕ => (0 : ℝ)) h :=
    fun h _hmem c d hwindow =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_Ico_length_le_zero_of_nonneg
        t ht_nonneg ha hwindow
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_canonical_zero_resonanceWindow_length_radicand
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint
      (fun _ : ℕ => (0 : ℝ)) hgap_pi hlength hrad

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

/-- Positive long-branch real-phase estimate from scaled-reciprocal
no-winding, positive-branch empty zero-centered resonance windows, and the
enlarged-envelope radicand target. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_zero_resonanceWindow_empty_radicand
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
    (hscaled_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                Real.pi)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  (((0 : ℝ) +
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
  have hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_gap_pi_of_scaled_reciprocal_family
      t ht_nonneg ha hscaled_pi
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_zero_resonanceWindow_empty_radicand
      t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint hgap_pi hrad

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

/-- Lower endpoint of the positive-frequency long shifted-increment range. -/
abbrev Real.logarithmicPhaseRealPhase_longIncrementLo : ℝ :=
  0

/-- Upper endpoint of the positive-frequency long shifted-increment range. -/
abbrev Real.logarithmicPhaseRealPhase_longIncrementHi
    (t : ℝ)
    (a h : ℕ) : ℝ :=
  t * ((h : ℝ) / ((a * (a + h + 1) : ℕ) : ℝ))

/-- The canonical long curvature-spread scale is positive on every Weyl
shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 < Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h := by
  intro h hh
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hh_pos : 0 < (h : ℝ) :=
    Nat.cast_pos.mpr
      (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
  have hnum_pos : 0 < ‖t‖ * (h : ℝ) :=
    mul_pos hT_pos hh_pos
  have hB_pos : 0 < ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBsq_pos :
      0 <
        ((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ))) :=
    mul_pos hB_pos (mul_pos hB_pos hB_pos)
  exact div_pos hnum_pos hBsq_pos

/-- The capped canonical thickness has square bounded by the curvature-spread
scale.  This is the local normalization behind the `eta = sqrt rho`
resonance decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longEta_sq_le_longRho
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h *
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h ≤
          Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h := by
  intro h hh
  let eta : ℝ := Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h
  let rho : ℝ := Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h
  have heta_nonneg : 0 ≤ eta := by
    exact le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b) h hh)
  have hrho_nonneg : 0 ≤ rho := by
    exact le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b) h hh)
  have heta_le_sqrt :
      eta ≤ Real.sqrt rho := by
    unfold eta rho
    exact min_le_right Real.pi
      (Real.sqrt
        (‖t‖ * (h : ℝ) /
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))))))
  have hsquare_le :
      eta * eta ≤ Real.sqrt rho * Real.sqrt rho :=
    mul_le_mul heta_le_sqrt heta_le_sqrt heta_nonneg
      (Real.sqrt_nonneg rho)
  have hsqrt_square :
      Real.sqrt rho * Real.sqrt rho = rho := by
    calc
      Real.sqrt rho * Real.sqrt rho = (Real.sqrt rho) ^ 2 :=
        (pow_two (Real.sqrt rho)).symm
      _ = rho :=
        Real.sq_sqrt hrho_nonneg
  exact
    Eq.subst
      (motive := fun right : ℝ => eta * eta ≤ right)
      hsqrt_square
      hsquare_le

/-- The canonical resonant-window budget is exactly the endpoint-spread
majorant required by the finite active-center wrapper. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_majorizes
    (T : ℝ)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength T) →
        (2 * Real.logarithmicPhaseRealPhase_longEta T b h) /
              Real.logarithmicPhaseRealPhase_longRho T b h +
            1 ≤
          Real.logarithmicPhaseRealPhase_longWindowBudget T b h := by
  intro h _hh
  exact le_refl _

/-- The canonical shifted-increment range contains every positive-frequency
shifted logarithmic increment on the long branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_mem_canonicalLongIncrementRange
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ n : ℕ,
          n ∈ Finset.Ico a (b - h) →
            Real.logarithmicPhaseRealPhase_longIncrementLo ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  n ∧
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  n ≤
                Real.logarithmicPhaseRealPhase_longIncrementHi t a h := by
  intro h _hh n hn
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_left_scaled_reciprocal_range
      t ht_nonneg ha hn

/-- The canonical long curvature-spread scale supplies the endpoint-spread
lower bound for every resonant window. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longRho_rational_endpoint_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ k : ℤ,
          ∀ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ))
                (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) =
              Finset.Ico c d →
            c < d - 1 →
              Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h *
                  (((d - 1) - c : ℕ) : ℝ) ≤
                ‖t‖ *
                  (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                    ((h : ℝ) /
                      (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) := by
  intro h hh k c d hwindow hcd
  have hh_pos : 1 ≤ h :=
    Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh
  have hcd_le : c < d :=
    lt_of_lt_of_le hcd (Nat.pred_le d)
  have hendpoint :
      a ≤ c ∧ d ≤ b - h :=
    Complex.realPhase_integerIncrementResonanceWindow_endpoint_bounds_of_eq_Ico
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hwindow
      hcd_le
  have hcore :
      ‖t‖ * (h : ℝ) * (((d - 1) - c : ℕ) : ℝ) /
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))) ≤
        ‖t‖ *
          (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
            ((h : ℝ) /
              (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) :=
    Real.logarithmicPhase_cubic_endpoint_spread_le
      ‖t‖ (norm_nonneg t) hh_pos hcd hendpoint.2
  have hleft_eq :
      Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h *
          (((d - 1) - c : ℕ) : ℝ) =
        ‖t‖ * (h : ℝ) * (((d - 1) - c : ℕ) : ℝ) /
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))) := by
    exact div_mul_eq_mul_div (‖t‖ * (h : ℝ))
      (((d - 1) - c : ℕ) : ℝ)
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ))))
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          ‖t‖ *
            (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
              ((h : ℝ) /
                (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))))
      hleft_eq.symm
      hcore

/-- The canonical resonant-window budget is nonnegative. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h := by
  intro h hh
  have heta_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b) h hh)
  have hrho_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b) h hh)
  have htwo_eta_nonneg :
      0 ≤ 2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    mul_nonneg zero_le_two heta_nonneg
  have hquot_nonneg :
      0 ≤
        (2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
    div_nonneg htwo_eta_nonneg hrho_nonneg
  exact add_nonneg hquot_nonneg zero_le_one

/-- On long blocks, the canonical long resonance thickness is at most `π`. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_longEta_le_pi_of_sqrt_long
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h ≤ Real.pi := by
  intro h hh
  exact min_le_left Real.pi
    (Real.sqrt
      (‖t‖ * (h : ℝ) /
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))))))

/-- The square-root normalization `η² ≤ ρ` converts the resonant-window
budget into the canonical second-derivative scale for one Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_longWindowBudget_le_sqrtScale
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h ≤
          2 *
              (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ +
            1 := by
  intro h hh
  let eta : ℝ := Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h
  let rho : ℝ := Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h
  have heta_pos : 0 < eta :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
      t ht (b := b) h hh
  have hrho_pos : 0 < rho :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
      t ht (b := b) h hh
  have heta_sq_le_rho : eta * eta ≤ rho := by
    unfold eta rho
    exact
      Complex.logarithmicPhaseRealPhase_shiftRange_longEta_sq_le_longRho
        t ht (b := b) h hh
  have heta_inv_nonneg : 0 ≤ eta⁻¹ :=
    inv_nonneg.mpr (le_of_lt heta_pos)
  have heta_le_rho_mul_inv :
      eta ≤ rho * eta⁻¹ := by
    have hmul :
        eta * eta * eta⁻¹ ≤ rho * eta⁻¹ :=
      mul_le_mul_of_nonneg_right heta_sq_le_rho heta_inv_nonneg
    have hleft :
        eta * eta * eta⁻¹ = eta := by
      calc
        eta * eta * eta⁻¹ = eta * (eta * eta⁻¹) :=
          mul_assoc eta eta eta⁻¹
        _ = eta * 1 := by
          exact congrArg (fun r : ℝ => eta * r)
            (mul_inv_cancel₀ (ne_of_gt heta_pos))
        _ = eta :=
          mul_one eta
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ rho * eta⁻¹)
        hleft.symm
        hmul
  have htwo_eta :
      2 * eta ≤ (2 * eta⁻¹) * rho := by
    have hscaled :
        2 * eta ≤ 2 * (rho * eta⁻¹) :=
      mul_le_mul_of_nonneg_left heta_le_rho_mul_inv zero_le_two
    have hright :
        2 * (rho * eta⁻¹) = (2 * eta⁻¹) * rho := by
      calc
        2 * (rho * eta⁻¹) = (2 * rho) * eta⁻¹ :=
          (mul_assoc 2 rho eta⁻¹).symm
        _ = (rho * 2) * eta⁻¹ := by
          exact congrArg (fun r : ℝ => r * eta⁻¹) (mul_comm 2 rho)
        _ = rho * (2 * eta⁻¹) :=
          mul_assoc rho 2 eta⁻¹
        _ = (2 * eta⁻¹) * rho :=
          mul_comm rho (2 * eta⁻¹)
    exact
      Eq.subst
        (motive := fun right : ℝ => 2 * eta ≤ right)
        hright
        hscaled
  have hquot :
      (2 * eta) / rho ≤ 2 * eta⁻¹ :=
    (div_le_iff₀ hrho_pos).mpr htwo_eta
  have hbudget :
      (2 * eta) / rho + 1 ≤ 2 * eta⁻¹ + 1 :=
    add_le_add_right hquot 1
  exact hbudget

/-- The displayed active-center decomposition budget is monotone in the
number of active centers. -/
theorem Real.logarithmicPhaseRealPhase_activeCenterBudget_mono
    {A C P : ℕ}
    {W G : ℝ}
    (hAC : A ≤ C)
    (hW : 0 ≤ W)
    (hG : 0 ≤ G) :
    (((A : ℝ) * W +
        (((((A + 1 : ℕ) * P : ℕ) : ℝ) * G)) +
      1) ≤
      (((C : ℝ) * W +
          (((((C + 1 : ℕ) * P : ℕ) : ℝ) * G)) +
        1) := by
  have hA_real : (A : ℝ) ≤ (C : ℝ) :=
    Nat.cast_le.mpr hAC
  have hfirst : (A : ℝ) * W ≤ (C : ℝ) * W :=
    mul_le_mul_of_nonneg_right hA_real hW
  have hsucc : A + 1 ≤ C + 1 :=
    Nat.succ_le_succ hAC
  have hmul_nat : (A + 1) * P ≤ (C + 1) * P :=
    Nat.mul_le_mul_right P hsucc
  have hmul_real :
      ((((A + 1 : ℕ) * P : ℕ) : ℝ) * G) ≤
        ((((C + 1 : ℕ) * P : ℕ) : ℝ) * G) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmul_nat) hG
  have hsum :
      (A : ℝ) * W +
          ((((A + 1 : ℕ) * P : ℕ) : ℝ) * G) ≤
        (C : ℝ) * W +
          ((((C + 1 : ℕ) * P : ℕ) : ℝ) * G) :=
    add_le_add hfirst hmul_real
  exact add_le_add_right hsum 1

/-- The displayed one-family active-center decomposition budget is monotone in
the number of active centers. -/
theorem Real.logarithmicPhaseRealPhase_activeCenterBudget_mono_one
    {A C : ℕ}
    {W G : ℝ}
    (hAC : A ≤ C)
    (hW : 0 ≤ W)
    (hG : 0 ≤ G) :
    (((A : ℝ) * W + (((A + 1 : ℕ) : ℝ) * G)) + 1) ≤
      (((C : ℝ) * W + (((C + 1 : ℕ) : ℝ) * G)) + 1) := by
  have hA_real : (A : ℝ) ≤ (C : ℝ) :=
    Nat.cast_le.mpr hAC
  have hfirst : (A : ℝ) * W ≤ (C : ℝ) * W :=
    mul_le_mul_of_nonneg_right hA_real hW
  have hsucc : A + 1 ≤ C + 1 :=
    Nat.succ_le_succ hAC
  have hsucc_real :
      (((A + 1 : ℕ) : ℝ) * G) ≤ (((C + 1 : ℕ) : ℝ) * G) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hsucc) hG
  have hsum :
      (A : ℝ) * W + (((A + 1 : ℕ) : ℝ) * G) ≤
        (C : ℝ) * W + (((C + 1 : ℕ) : ℝ) * G) :=
    add_le_add hfirst hsucc_real
  exact add_le_add_right hsum 1

end

end LFunctions
end Boundary
