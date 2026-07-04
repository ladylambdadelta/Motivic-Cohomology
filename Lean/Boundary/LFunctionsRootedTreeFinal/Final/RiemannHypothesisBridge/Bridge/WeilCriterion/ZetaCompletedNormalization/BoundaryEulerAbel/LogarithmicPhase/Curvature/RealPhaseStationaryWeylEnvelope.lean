import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseStationaryVdc

/-!
# Real-phase stationary Weyl-envelope wrapper

This file substitutes the logarithmic shifted-correlation curvature majorants
into the finite second-derivative Weyl envelope.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Logarithmic Weyl-envelope bound with the shifted-correlation envelope
replaced by explicit curvature majorants. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_le_weylEnvelope_curvatureMajorants
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
              (h : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hH :
      1 ≤ Real.secondDerivativeVdc_weylShiftLength ‖t‖ :=
    Real.one_le_secondDerivativeVdc_weylShiftLength ht
  have hH_block :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤
        (Finset.Icc a b).card :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_card_of_sqrt_long
      ht hab hlong_sqrt
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
            φ a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) :=
    @Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weylEnvelope
      φ a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
      hH hH_block
  have hmajorant :
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
            φ a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    @Real.secondDerivativeVdc_weylEnvelopeMajorant_mono
      a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
      (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        φ a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖))
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)
      hH
      (Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_curvatureMajorants
        t ht ha hlong_sqrt hderiv_growth
        hderiv_antitone hinc_mono hred_mono hsep)
  exact le_trans hweyl hmajorant

end

end LFunctions
end Boundary
