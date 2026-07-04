import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseIntervalReduction

/-!
# Real-phase endpoint first-derivative estimates

This file owns the non-circular first-derivative endpoint estimate used by the
endpoint packet contribution layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Under the global logarithmic lower bound, the square-root scale dominates
one. -/
theorem Real.logarithmicPhase_one_le_sqrt_one_add_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
  have hone_le_inner : (1 : ℝ) ≤ 1 + ‖t‖ :=
    le_trans ht (le_add_of_nonneg_left zero_le_one)
  have hone_sq : (1 : ℝ) ^ 2 = 1 :=
    one_pow 2
  have hsq_le_inner : (1 : ℝ) ^ 2 ≤ 1 + ‖t‖ :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ 1 + ‖t‖)
      hone_sq.symm
      hone_le_inner
  exact Real.le_sqrt_of_sq_le hsq_le_inner

/-- Replacing the harmless `+ 1` in the first-derivative target by the
second-derivative square-root scale only enlarges the target. -/
theorem Real.logarithmicPhase_endpoint_one_le_endpoint_sqrt_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (r : ℕ) :
    (((r + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
      (((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  exact
    add_le_add_left
      (Real.logarithmicPhase_one_le_sqrt_one_add_norm t ht)
      (((r + 1 : ℕ) : ℝ) / ‖t‖)

/-- The concrete logarithmic first-derivative estimate on a subblock, widened
to the ambient endpoint-plus-square-root target.  The finite-difference
monotonicity and separation data remain explicit inputs. -/
theorem Complex.logarithmicPhaseRealPhase_firstDerivative_subblock_le_twentyTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c r : ℕ}
    (hc_one : 1 ≤ c)
    (hcr : c ≤ r)
    (hr_right : r ≤ b)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c r)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c r)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c r
        (‖t‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc c r,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block
      t hc_one hcr
  have hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (c : ℝ) ((r + 1 : ℕ) : ℝ) →
          ((‖t‖ : ℝ) / ((r + 1 : ℕ) : ℝ)) ≤
            ‖deriv φ x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound
        t hc_one hcr hx
  have hfirst :
      ‖∑ n ∈ Finset.Icc c r,
        Complex.exp
          (Complex.I *
            (φ n : ℂ))‖ ≤
        20 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
      t ht hc_one hcr
      hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep
  have hone_to_sqrt :
      20 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + 1)) ≤
        20 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_le_mul_of_nonneg_left
      (Real.logarithmicPhase_endpoint_one_le_endpoint_sqrt_target t ht r)
      (Nat.cast_nonneg 20)
  have hright_mono :
      20 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_le_mul_of_nonneg_left
      (Real.logarithmicPhase_endpoint_sqrt_target_mono_right t ht hr_right)
      (Nat.cast_nonneg 20)
  exact le_trans hfirst (le_trans hone_to_sqrt hright_mono)

end

end LFunctions
end Boundary
