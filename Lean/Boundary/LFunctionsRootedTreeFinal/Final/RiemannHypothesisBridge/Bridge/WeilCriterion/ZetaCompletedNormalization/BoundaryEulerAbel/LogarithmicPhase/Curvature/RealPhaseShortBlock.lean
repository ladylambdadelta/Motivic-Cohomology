import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseIntervalReduction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.SecondDerivativeVdc

/-!
# Real-phase short block estimates

This file owns the short-branch reductions in the logarithmic real-phase
curvature block estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A singleton logarithmic real-phase block satisfies the widened curvature
target. -/
theorem Complex.logarithmicPhaseRealPhase_singleton_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a : ℕ) :
    ‖∑ n ∈ Finset.Icc a a,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hbase :
      ‖∑ n ∈ Finset.Icc a a,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        (((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
    Complex.realPhase_secondDerivative_vdc_singleton_integer_block_bound
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a ht
  have hwiden :
      (((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
        80 * ((((a + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Real.logarithmicPhase_target_le_eighty_mul
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht a)
  exact le_trans hbase hwiden

/-- If the integer block cardinality is already below the widened curvature
target, the logarithmic real-phase block satisfies the target by the trivial
unit-norm estimate. -/
theorem Complex.logarithmicPhaseRealPhase_card_le_eightyTarget_block_bound
    (t : ℝ)
    {a b : ℕ}
    (hcard :
      ((Finset.Icc a b).card : ℝ) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have htrivial :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        ((Finset.Icc a b).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
  exact le_trans htrivial hcard

/-- If the block length is at most the square-root scale, the logarithmic
real-phase block satisfies the widened curvature target. -/
theorem Complex.logarithmicPhaseRealPhase_short_sqrt_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab_succ : a ≤ b + 1)
    (hlength :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ Real.sqrt (1 + ‖t‖)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hbase :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_sqrt
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ht hlength hab_succ
  have hwiden :
      (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Real.logarithmicPhase_target_le_eighty_mul
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  exact le_trans hbase hwiden

/-- If the block length is at most the endpoint derivative scale, the
logarithmic real-phase block satisfies the widened curvature target. -/
theorem Complex.logarithmicPhaseRealPhase_short_endpoint_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab_succ : a ≤ b + 1)
    (hlength :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ (((b + 1 : ℕ) : ℝ) / ‖t‖)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hbase :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_endpoint
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ht hlength hab_succ
  have hwiden :
      (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Real.logarithmicPhase_target_le_eighty_mul
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  exact le_trans hbase hwiden

/-- A real-phase block estimate for `-t` transports to the corresponding
estimate for `t`, since the two block sums have the same norm. -/
theorem Complex.logarithmicPhaseRealPhase_block_bound_of_neg_parameter_bound
    (t : ℝ)
    {a b : ℕ}
    (hneg :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖-t‖ + Real.sqrt (1 + ‖-t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hneg_norm : ‖-t‖ = ‖t‖ :=
    norm_neg t
  have htarget_eq :
      80 * ((((b + 1 : ℕ) : ℝ) / ‖-t‖ + Real.sqrt (1 + ‖-t‖))) =
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    congrArg
      (fun r : ℝ =>
        80 * ((((b + 1 : ℕ) : ℝ) / r + Real.sqrt (1 + r))))
      hneg_norm
  have hnorm_eq :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ :=
    Complex.logarithmicPhaseRealPhase_block_norm_neg_parameter_eq t a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hnorm_eq
      (Eq.subst
        (motive := fun right : ℝ =>
          ‖∑ n ∈ Finset.Icc a b,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase (-t) n : ℂ))‖ ≤
            right)
        htarget_eq
        hneg)

end

end LFunctions
end Boundary
