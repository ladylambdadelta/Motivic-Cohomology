import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseNoWinding
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseStationaryWeylEnvelope

/-!
# Real-phase long Weyl target

This file owns the finite target transport from the logarithmic Weyl-envelope
bound to the long-branch target.  The remaining analytic input is the explicit
curvature-majorant Weyl-envelope target estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The logarithmic Weyl-envelope estimate gives the long target from any
proved shifted-correlation envelope bound. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_shiftedCorrelationEnvelope_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {E : ℝ}
    (henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤ E)
    (hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) E ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hH :
      1 ≤ Real.secondDerivativeVdc_weylShiftLength ‖t‖ :=
    Real.one_le_secondDerivativeVdc_weylShiftLength ht
  have hH_block :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤
        (Finset.Icc a b).card :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_card_of_sqrt_long
      ht hab hlong_sqrt
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) :=
    @Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weylEnvelope
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
      hH hH_block
  have hmajorant :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) E :=
    @Real.secondDerivativeVdc_weylEnvelopeMajorant_mono
      a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
      (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖))
      E hH henvelope
  exact le_trans (le_trans hweyl hmajorant) hweyl_target

/-- Radicand form of the arbitrary shifted-correlation envelope transport. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {E : ℝ}
    (henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤ E)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 * E) *
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
      0 ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) := by
    have hden_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    have hdiv_nonneg :
        0 ≤ (((b + 1 : ℕ) : ℝ) / ‖t‖) :=
      div_nonneg (Nat.cast_nonneg (b + 1)) (le_of_lt hden_pos)
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 + ‖t‖) :=
      Real.sqrt_nonneg (1 + ‖t‖)
    exact
      mul_nonneg
        (show (0 : ℝ) ≤ 80 from Nat.cast_nonneg 80)
        (add_nonneg hdiv_nonneg hsqrt_nonneg)
  have hweyl_target :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) E ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hweyl_target

/-- The logarithmic Weyl-envelope estimate gives the long target once the
curvature-majorant envelope has been bounded by that target. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
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
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_block_norm_le_weylEnvelope_curvatureMajorants
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep
  exact le_trans hweyl hweyl_target

/-- The logarithmic Weyl-envelope estimate gives the long target once the
explicit Weyl-envelope radicand is bounded by the square of that target. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hweyl_target

/-- Positive-frequency long Weyl-target wrapper with the parent curvature
growth and shifted-derivative antitonicity discharged from the logarithmic
curvature owner lemmas. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u) :=
    Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
      t ht ht_nonneg ha hab
  have hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hweyl_target

/-- Positive-frequency long Weyl-target wrapper with the parent curvature
growth and shifted-derivative antitonicity discharged, leaving only the
explicit Weyl-envelope radicand target. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u) :=
    Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
      t ht ht_nonneg ha hab
  have hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hrad

/-- Positive-frequency long Weyl-target wrapper with raw shifted-increment
monotonicity discharged by the fixed-width logarithmic gap theorem. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_reduced_sep
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
      hinc_mono hred_mono hsep hweyl_target

/-- Positive-frequency long Weyl-target wrapper with raw shifted-increment
monotonicity and no-winding principal-interval control discharged by the
logarithmic gap owner lemmas. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_principal_sep
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hprincipal :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
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
    fun h hmem =>
      Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        (hinc_mono h hmem)
        (hprincipal h hmem)
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
      hinc_mono hred_mono hsep hweyl_target

/-- Positive-frequency long Weyl-target wrapper with no-winding discharged from
pointwise `π` bounds on the shifted logarithmic increments. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_gap_pi_sep
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hprincipal :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    fun h hmem n hn =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_principal_of_gap_pi
        t ht_nonneg ha hn
        (hgap_pi h hmem n hn)
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_principal_sep
      t ht ht_nonneg ha hab hlong_sqrt hprincipal hsep hweyl_target

/-- Positive-frequency `π` gap bounds put every shifted logarithmic increment
on the principal branch, so raw shifted monotonicity transfers to reduced
shifted monotonicity throughout the Weyl shift range. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_reduced_mono_of_gap_pi
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
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
                n ≤ Real.pi) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Complex.realPhase_reducedIntegerIncrementMonotoneOn
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) := by
  intro h hmem
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
      t ht_nonneg ha
  have hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    fun n hn =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_principal_of_gap_pi
        t ht_nonneg ha hn (hgap_pi h hmem n hn)
  exact
    Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hinc_mono
      hprincipal

/-- A family of scaled rational fixed-width gap estimates supplies the
pointwise `π` bounds needed for no-winding of every shifted logarithmic
increment in the Weyl shift range. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_gap_pi_of_scaled_reciprocal_family
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hscaled_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                Real.pi) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ n : ℕ,
          n ∈ Finset.Ico a (b - h) →
            Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n ≤ Real.pi := by
  intro h hmem n hn
  have hn_bounds : a ≤ n ∧ n < b - h :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans ha hn_bounds.1
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_pi_of_scaled_reciprocal
      t ht_nonneg hn_one (hscaled_pi h hmem n hn)

/-- Resonance-window avoidance plus the pointwise `π` gap bound supplies the
shifted separation input for the positive-frequency long Weyl target. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_sep_of_gap_pi_resonanceWindow_avoidance
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
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
              n ∉ S h) :
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
            (h : ℝ)) := by
  intro h hmem
  have hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    fun n hn =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_principal_of_gap_pi
        t ht_nonneg ha hn
        (hgap_pi h hmem n hn)
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (S h)
      rfl
      (hS h hmem)
      (fun n hn => hn)
      (havoid h hmem)
      hprincipal

/-- The left side of a canonical zero-centered resonance window for a shifted
logarithmic difference is separated under the pointwise `π` gap bound. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_left_sep_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ)) lam =
        Finset.Ico c d) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      a c lam := by
  have hcb : c ≤ b - h :=
    le_trans hcd hdb
  have hleft_sub :
      Finset.Ico a c ⊆ Finset.Ico a (b - h) :=
    Finset.Ico_left_subset_ambient_of_le hcb
  have hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a c →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    fun n hn =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_principal_of_gap_pi
        t ht_nonneg ha (hleft_sub hn) (hgap_pi n (hleft_sub hn))
  exact
    Complex.realPhase_integerIncrementSeparatedOn_left_of_canonical_zero_resonanceWindow_eq_Ico_principal
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hac hcd hdb hwindow hprincipal

/-- The right side of a canonical zero-centered resonance window for a shifted
logarithmic difference is separated under the pointwise `π` gap bound. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_right_sep_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ)) lam =
        Finset.Ico c d) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      d (b - h) lam := by
  have had : a ≤ d :=
    le_trans hac hcd
  have hright_sub :
      Finset.Ico d (b - h) ⊆ Finset.Ico a (b - h) :=
    Finset.Ico_right_subset_ambient_of_le had
  have hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico d (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
    fun n hn =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_principal_of_gap_pi
        t ht_nonneg ha (hright_sub hn) (hgap_pi n (hright_sub hn))
  exact
    Complex.realPhase_integerIncrementSeparatedOn_right_of_canonical_zero_resonanceWindow_eq_Ico_principal
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hac hcd hdb hwindow hprincipal

/-- A shifted-logarithmic side `Ico` sum is bounded by the curvature
shifted-correlation majorant once all terminal closed subblocks have that
majorant bound. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_terminal_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c d h : ℕ}
    (hpos : 1 ≤ h)
    (hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp
                (Complex.I *
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h n : ℂ))‖ ≤
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  have htarget_nonneg :
      0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
    Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_of_terminal_Icc_bounds
      t htarget_nonneg hIcc

/-- Terminal closed subblocks of a shifted-logarithmic side interval are
bounded by the curvature shifted-correlation majorant from the first-derivative
data on each terminal subblock. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_terminal_Icc_sum_norm_le_curvatureMajorant_of_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c h r : ℕ}
    (hc : 1 ≤ c)
    (hcr : c ≤ r)
    (hpos : 1 ≤ h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c r)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c r)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c r
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))) :
    ‖∑ n ∈ Finset.Icc c r,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  let lam : ℝ :=
    ‖t‖ *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹) *
      (h : ℝ)
  have hlam_pos : 0 < lam :=
    Real.secondDerivativeVdc_shiftedLowerParameter_pos ht hpos
  have hfirst :
      ‖∑ n ∈ Finset.Icc c r,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
    Complex.realPhase_firstDerivative_integer_block_bound
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hc hcr hlam_pos hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep
  exact hfirst

/-- A shifted-logarithmic side interval is bounded by the curvature
shifted-correlation majorant when every terminal closed subblock has the
corresponding first-derivative data. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_terminal_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c d h : ℕ}
    (hc : 1 ≤ c)
    (hpos : 1 ≤ h)
    (hderiv_antitone :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            AntitoneOn
              (fun x : ℝ =>
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h) x‖)
              (Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ∀ x : ℝ,
              x ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ) →
                ‖t‖ *
                    ((((b + 1 : ℕ) : ℝ) *
                      (((b + 1 : ℕ) : ℝ)))⁻¹) *
                    (h : ℝ) ≤
                  ‖deriv
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h) x‖)
    (hinc_mono :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            Complex.realPhase_integerIncrementMonotoneOn
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              c r)
    (hred_mono :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            Complex.realPhase_reducedIntegerIncrementMonotoneOn
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              c r)
    (hsep :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            Complex.realPhase_integerIncrementSeparatedOn
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              c r
              (‖t‖ *
                ((((b + 1 : ℕ) : ℝ) *
                  (((b + 1 : ℕ) : ℝ)))⁻¹) *
                (h : ℝ))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_terminal_Icc_bounds
      t ht hpos
      (fun {r} hcr hrd =>
        Complex.logarithmicPhaseRealPhase_shiftedDifference_terminal_Icc_sum_norm_le_curvatureMajorant_of_firstDerivative_data
          (t := t)
          (ht := ht)
          (b := b)
          (c := c)
          (h := h)
          (r := r)
          hc hcr hpos
          (hderiv_antitone hcr hrd)
          (hderiv_lower hcr hrd)
          (hinc_mono hcr hrd)
          (hred_mono hcr hrd)
          (hsep hcr hrd))

/-- A shifted-logarithmic side interval is bounded by the curvature
shifted-correlation majorant when it lies inside the ambient shifted interval,
the ambient shifted first-derivative and monotonicity data are available, and
the side interval itself is separated. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_deriv_mono_local_sep
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c d h : ℕ}
    (hc : 1 ≤ c)
    (hac : a ≤ c)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c d
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_terminal_firstDerivative_data
      (t := t)
      (ht := ht)
      (b := b)
      (c := c)
      (d := d)
      (h := h)
      hc hpos
      (fun {r} _hcr hrd =>
        have hrd_le_B : r + 1 ≤ (b - h) :=
          Eq.subst
            (motive := fun right : ℕ => right ≤ b - h)
            hrd.symm
            hdb
        fun x hx y hy hxy =>
          have hx_bounds : (c : ℝ) ≤ x ∧ x ≤ ((r + 1 : ℕ) : ℝ) :=
            hx
          have hy_bounds : (c : ℝ) ≤ y ∧ y ≤ ((r + 1 : ℕ) : ℝ) :=
            hy
          have hx_ambient : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) :=
            And.intro
              (le_trans (Nat.cast_le.mpr hac) hx_bounds.1)
              (le_trans hx_bounds.2
                (Nat.cast_le.mpr
                  (Nat.le_trans hrd_le_B (Nat.le_succ (b - h)))))
          have hy_ambient : y ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) :=
            And.intro
              (le_trans (Nat.cast_le.mpr hac) hy_bounds.1)
              (le_trans hy_bounds.2
                (Nat.cast_le.mpr
                  (Nat.le_trans hrd_le_B (Nat.le_succ (b - h)))))
          hderiv_antitone hx_ambient hy_ambient hxy)
      (fun {r} _hcr hrd x hx =>
        have hrd_le_B : r + 1 ≤ (b - h) :=
          Eq.subst
            (motive := fun right : ℕ => right ≤ b - h)
            hrd.symm
            hdb
        have hx_bounds : (c : ℝ) ≤ x ∧ x ≤ ((r + 1 : ℕ) : ℝ) :=
          hx
        have hx_ambient : x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) :=
          And.intro
            (le_trans (Nat.cast_le.mpr hac) hx_bounds.1)
            (le_trans hx_bounds.2
              (Nat.cast_le.mpr
                (Nat.le_trans hrd_le_B (Nat.le_succ (b - h)))))
        hderiv_lower x hx_ambient)
      (fun {r} _hcr hrd =>
        have hr_le_B : r ≤ b - h := by
          have hsucc_le : r + 1 ≤ b - h :=
            Eq.subst
              (motive := fun right : ℕ => right ≤ b - h)
              hrd.symm
              hdb
          exact Nat.le_trans (Nat.le_succ r) hsucc_le
        Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          hinc_mono
          (Finset.Ico_subset_Ico hac hr_le_B))
      (fun {r} _hcr hrd =>
        have hr_le_B : r ≤ b - h := by
          have hsucc_le : r + 1 ≤ b - h :=
            Eq.subst
              (motive := fun right : ℕ => right ≤ b - h)
              hrd.symm
              hdb
          exact Nat.le_trans (Nat.le_succ r) hsucc_le
        Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          hred_mono
          (Finset.Ico_subset_Ico hac hr_le_B))
      (fun {r} _hcr hrd =>
        have hrd_le_d : r ≤ d :=
          Eq.subst
            (motive := fun right : ℕ => r ≤ right)
            hrd
            (Nat.le_succ r)
        Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          hsep
          (Finset.Ico_subset_Ico (le_refl c) hrd_le_d))

/-- A shifted-logarithmic side interval is bounded by the curvature
shifted-correlation majorant when it lies inside the ambient shifted interval
and all ambient first-derivative, monotonicity, and separation data are
available. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c d h : ℕ}
    (hc : 1 ≤ c)
    (hac : a ≤ c)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_deriv_mono_local_sep
      t ht hc hac hdb hpos hderiv_antitone hderiv_lower hinc_mono hred_mono
      (Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        hsep
      (Finset.Ico_subset_Ico hac hdb))

/-- A shifted-logarithmic interval assigned to an integer lattice center has
the standard curvature-majorant bound after subtracting that lattice slope.
The subtraction preserves all integer exponential samples, while the
resonance-window avoidance supplies monotone separated increments for the
shifted phase. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_integerLatticeShift_gap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c d h : ℕ}
    {lam : ℝ}
    (k : ℤ)
    (hc : 1 ≤ c)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hsub : Finset.Ico c d ⊆ Finset.Ico a (b - h))
    (havoid :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          n ∉ Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                k)
              n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  let ψ : ℝ → ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedDifference
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      h
  let ψk : ℝ → ℝ :=
    Complex.realPhase_integerLatticeShift ψ k
  have hlam_pos_raw :
      0 <
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ) :=
    Real.secondDerivativeVdc_shiftedLowerParameter_pos ht hpos
  have hlam_pos : 0 < lam :=
    Eq.subst
      (motive := fun r : ℝ => 0 < r)
      hlam.symm
      hlam_pos_raw
  have hinputs :
      Complex.realPhase_integerIncrementMonotoneOn ψk c d ∧
        Complex.realPhase_reducedIntegerIncrementMonotoneOn ψk c d ∧
        Complex.realPhase_integerIncrementSeparatedOn ψk c d lam :=
    Complex.realPhase_integerLatticeShift_gap_finiteDifference_inputs
      ψ k hinc_mono hsub havoid hprincipal
  have hM_nonneg :
      0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
    Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg ht hpos
  have hIcc :
      ∀ {r : ℕ},
        c ≤ r →
          r + 1 = d →
            ‖∑ n ∈ Finset.Icc c r,
              Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
    intro r hcr hrd
    have hrd_le : r ≤ d :=
      Eq.subst
        (motive := fun right : ℕ => r ≤ right)
        hrd
        (Nat.le_succ r)
    have hsubset_terminal : Finset.Ico c r ⊆ Finset.Ico c d :=
      Finset.Ico_subset_Ico (le_refl c) hrd_le
    have hmono_terminal :
        Complex.realPhase_integerIncrementMonotoneOn ψk c r :=
      Complex.realPhase_integerIncrementMonotoneOn.mono_Ico
        ψk hinputs.1 hsubset_terminal
    have hred_terminal :
        Complex.realPhase_reducedIntegerIncrementMonotoneOn ψk c r :=
      Complex.realPhase_reducedIntegerIncrementMonotoneOn.mono_Ico
        ψk hinputs.2.1 hsubset_terminal
    have hsep_terminal :
        Complex.realPhase_integerIncrementSeparatedOn ψk c r lam :=
      Complex.realPhase_integerIncrementSeparatedOn.mono_Ico
        ψk hinputs.2.2 hsubset_terminal
    have hsep_terminal_target :
        Complex.realPhase_integerIncrementSeparatedOn ψk c r
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) :=
      Eq.subst
        (motive := fun value : ℝ =>
          Complex.realPhase_integerIncrementSeparatedOn ψk c r value)
        hlam
        hsep_terminal
    have hshift :
        ‖∑ n ∈ Finset.Icc c r,
          Complex.exp (Complex.I * (ψk n : ℂ))‖ ≤
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
      Complex.realPhase_separatedIncrement_integer_block_bound
        ψk hc hcr
        (Real.secondDerivativeVdc_shiftedLowerParameter_pos ht hpos)
        hmono_terminal hred_terminal hsep_terminal_target
    exact
      Complex.realPhase_sum_norm_le_of_integerLatticeShift_sum_norm_le
        ψ k (Finset.Icc c r) hshift
  exact
    Complex.realPhase_Ico_sum_norm_le_of_terminal_Icc_bounds
      ψ hM_nonneg hIcc

/-- A shifted-logarithmic interval contained in the active resonance-family
complement has the standard curvature-majorant bound.  The active-family
complement supplies the lattice separation; the remaining data are inherited
from the ambient shifted interval. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_activeComplement
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c d h : ℕ}
    {lam : ℝ}
    (hc : 1 ≤ c)
    (hac : a ≤ c)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hlam :
      lam =
        ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
    (hgap_subset :
      Finset.Ico c d ⊆
        Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
          t a b h lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  have hsep_lam :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c d lam :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_Ico_separated
      t hgap_subset
  have hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        c d
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ)) :=
    Eq.subst
      (motive := fun r : ℝ =>
        Complex.realPhase_integerIncrementSeparatedOn
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          c d r)
      hlam
      hsep_lam
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_deriv_mono_local_sep
      t ht hc hac hdb hpos hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- The left side of a canonical zero-centered resonance window has the
standard curvature-majorant bound.  The derivative and monotonicity data are
used on the ambient shifted interval; separation is supplied by the canonical
window avoidance on the left side. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_left_Ico_sum_norm_le_curvatureMajorant_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    (ha : 1 ≤ a)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        Finset.Ico c d)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a c,
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  have hcb : c ≤ b - h :=
    le_trans hcd hdb
  have hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a c
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_left_sep_of_gap_pi_canonical_zero_resonanceWindow
      t ht_nonneg ha hac hcd hdb hgap_pi hwindow
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_deriv_mono_local_sep
      t ht ha (le_refl a) hcb hpos
      hderiv_antitone hderiv_lower hinc_mono hred_mono hsep

/-- The right side of a canonical zero-centered resonance window has the
standard curvature-majorant bound.  The derivative and monotonicity data are
used on the ambient shifted interval; separation is supplied by the canonical
window avoidance on the right side. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_right_Ico_sum_norm_le_curvatureMajorant_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    (ha : 1 ≤ a)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        Finset.Ico c d)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico d (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h := by
  have had : a ≤ d :=
    le_trans hac hcd
  have hd_pos : 1 ≤ d :=
    le_trans ha had
  have hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        d (b - h)
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_right_sep_of_gap_pi_canonical_zero_resonanceWindow
      t ht_nonneg ha hac hcd hdb hgap_pi hwindow
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_curvatureMajorant_of_ambient_deriv_mono_local_sep
      t ht hd_pos had (le_refl (b - h)) hpos
      hderiv_antitone hderiv_lower hinc_mono hred_mono hsep

/-- A shifted logarithmic correlation split around a canonical zero-centered
resonance window is bounded by the resonant-window length budget and the two
curvature-majorant side bounds. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_windowLength_add_two_curvatureMajorants_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    {M : ℝ}
    (ha : 1 ≤ a)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        Finset.Ico c d)
    (hlength : ((d - c : ℕ) : ℝ) ≤ M)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖∑ n ∈ Finset.Ico a (b - h),
      Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h n : ℂ))‖ ≤
      M +
        (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  have hsplit :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ))
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ +
          (‖∑ n ∈ Finset.Ico a c,
            Complex.exp
              (Complex.I *
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h n : ℂ))‖ +
            ‖∑ n ∈ Finset.Ico d (b - h),
              Complex.exp
                (Complex.I *
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h n : ℂ))‖) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_window_add_left_add_right_of_eq_Ico
      t hac hcd hdb hwindow
  have hwindow_bound :
      ‖∑ n ∈ Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤ M :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_sum_norm_le_of_Ico_length
      t hwindow hlength
  have hleft :
      ‖∑ n ∈ Finset.Ico a c,
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_left_Ico_sum_norm_le_curvatureMajorant_of_gap_pi_canonical_zero_resonanceWindow
      t ht ht_nonneg ha hac hcd hdb hpos hgap_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  have hright :
      ‖∑ n ∈ Finset.Ico d (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_right_Ico_sum_norm_le_curvatureMajorant_of_gap_pi_canonical_zero_resonanceWindow
      t ht ht_nonneg ha hac hcd hdb hpos hgap_pi hwindow
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    le_trans hsplit
      (add_le_add hwindow_bound (add_le_add hleft hright))

/-- Closed shifted correlations inherit the canonical zero-centered resonance
window split with the terminal endpoint contribution made explicit. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_windowLength_add_two_curvatureMajorants_add_one_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    {M : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b - h)
    (hpos : 1 ≤ h)
    (hgap_pi :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤ Real.pi)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        Finset.Ico c d)
    (hlength : ((d - c : ℕ) : ℝ) ≤ M)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
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
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      (M +
        (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) + 1 := by
  have hclosed :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  have hhalf :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h n : ℂ))‖ ≤
        M +
          (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_Ico_sum_norm_le_windowLength_add_two_curvatureMajorants_of_gap_pi_canonical_zero_resonanceWindow
      t ht ht_nonneg ha hac hcd hdb hpos hgap_pi hwindow hlength
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    le_trans hclosed
      (add_le_add_right hhalf 1)

/-- The shifted-correlation envelope inherits pointwise canonical
zero-centered resonance-window decompositions.  The right-hand side keeps the
resonant-window length budget, two side curvature majorants, and terminal
endpoint contribution visible for each Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_windowLength_add_two_curvatureMajorants_add_one_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
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
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        ((M h +
          (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) + 1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        ((M h +
          (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) + 1)
  exact
    Finset.sum_le_sum
      (fun h hmem =>
        let A : ℝ :=
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h
        have hpoint :
            ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
              (M h + A) + 1 :=
          Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_windowLength_add_two_curvatureMajorants_add_one_of_gap_pi_canonical_zero_resonanceWindow
            t ht ht_nonneg ha (habh h hmem) (hc h hmem) (hcd h hmem)
            (hdb h hmem)
            (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hmem)
            (hgap_pi h hmem) (hwindow h hmem) (hlength h hmem)
            (hderiv_antitone h hmem) (hderiv_lower h hmem)
            (hinc_mono h hmem) (hred_mono h hmem)
        hpoint)

/-- Positive-frequency long Weyl-target estimate from canonical zero-centered
resonance-window decompositions and a radicand bound for the resulting enlarged
shifted-correlation envelope. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg_of_gap_pi_canonical_zero_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  have habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h :=
    fun h hmem =>
      Nat.realPhase_secondDerivative_vdc_lower_le_sub_shift hgap hmem
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          ((M h +
            (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h +
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) + 1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_windowLength_add_two_curvatureMajorants_add_one_of_gap_pi_canonical_zero_resonanceWindow
      t ht ht_nonneg ha habh c d M hc hcd hdb hgap_pi hwindow hlength
      hderiv_antitone hderiv_lower hinc_mono hred_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- Positive-frequency long Weyl-target estimate from canonical zero-centered
resonance-window decompositions and the enlarged-envelope radicand target, with
the shifted derivative and monotonicity data discharged by the logarithmic
positive branch. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg_of_gap_pi_canonical_zero_resonanceWindow_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  have hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u) :=
    Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
      t ht ht_nonneg ha hab
  have hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
  have hderiv_lower :
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
                    h) x‖ :=
    fun h hmem x hx =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
        t ha
        (le_trans
          (Complex.realPhase_secondDerivative_vdc_shiftRange_le hmem)
          hgap)
        hx hderiv_growth
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_nonneg_of_gap_pi_canonical_zero_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt c d M hc hcd hdb hgap_pi hwindow
      hlength hderiv_antitone hderiv_lower hinc_mono hred_mono hrad

/-- Positive-frequency long Weyl-target wrapper with no-winding and separation
both discharged from pointwise `π` bounds and resonance-window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_gap_pi_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hsep :
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
              (h : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_sep_of_gap_pi_resonanceWindow_avoidance
      t ht_nonneg ha hgap_pi S hS havoid
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_gap_pi_sep
      t ht ht_nonneg ha hab hlong_sqrt hgap_pi hsep hweyl_target

/-- Avoidance of all integer-centered resonance windows supplies the shifted
separation input for the positive-frequency long Weyl target. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_sep_of_integer_resonanceWindow_avoidance
    (t : ℝ)
    {a b : ℕ}
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
                n ∉ S h k) :
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
            (h : ℝ)) := by
  intro h hmem
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_family_avoidance
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (S h)
      (hS h hmem)
      (fun n hn => hn)
      (havoid h hmem)

/-- Avoidance of the canonical integer-centered resonance windows supplies
the shifted separation input for the positive-frequency long Weyl target. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_sep_of_canonical_integer_resonanceWindow_avoidance
    (t : ℝ)
    {a b : ℕ}
    (havoid :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                n ∉
                  Complex.realPhase_integerIncrementResonanceWindow
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    a (b - h)
                    (2 * Real.pi * (k : ℝ))
                    (‖t‖ *
                      ((((b + 1 : ℕ) : ℝ) *
                        (((b + 1 : ℕ) : ℝ)))⁻¹) *
                      (h : ℝ))) :
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
            (h : ℝ)) := by
  intro h hmem
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_canonical_resonanceWindow_family_avoidance
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (fun n hn => hn)
      (havoid h hmem)

/-- Positive-frequency long Weyl-target wrapper with separation discharged by
avoidance of all integer-centered resonance windows.  This is the no-winding
free owner-level target for the long branch. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_integer_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
  have hsep :
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
              (h : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_sep_of_integer_resonanceWindow_avoidance
      t S hS havoid
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_reduced_sep
      t ht ht_nonneg ha hab hlong_sqrt hred_mono hsep hweyl_target

/-- Positive-frequency long Weyl-target wrapper with reduced monotonicity
discharged by fixed integer branch strips and separation discharged by
avoidance of all integer-centered resonance windows. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_integer_strip_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
    fun h hmem =>
      Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_integer_strip
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        (hinc_mono h hmem)
        (hstrip h hmem)
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_integer_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt hred_mono S hS havoid hweyl_target

/-- Positive-frequency long Weyl-target wrapper with no-winding discharged
from scaled reciprocal arithmetic and separation discharged from resonance
window avoidance. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_scaled_reciprocal_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_target_of_nonneg_of_gap_pi_resonanceWindow
      t ht ht_nonneg ha hab hlong_sqrt hgap_pi S hS havoid hweyl_target

end

end LFunctions
end Boundary
