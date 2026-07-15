import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFrequencyScaleSplit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcVariation

/-!
# Post-cutoff logarithmic increments

Beyond `floor ‖t‖`, every logarithmic adjacent increment has magnitude below
one.  It therefore lies in the principal `(-π,π]` interval, reduction modulo
`2π` is inactive, and reduced monotonicity follows from raw monotonicity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.nonneg_parameter_eq_norm
    (t : ℝ) (ht : 0 ≤ t) :
    t = ‖t‖ := by
  exact (Real.norm_of_nonneg ht).symm

theorem Real.norm_div_nat_lt_one_of_norm_lt_nat
    (t : ℝ) {n : ℕ}
    (hn : ‖t‖ < (n : ℝ)) :
    ‖t‖ / (n : ℝ) < 1 := by
  have hnPos : (0 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (norm_nonneg t) hn
  exact (div_lt_one hnPos).mpr hn

theorem Real.postCutoff_norm_div_index_lt_one
    (t : ℝ) {n : ℕ}
    (hn : Real.logarithmicPhaseFrequencyTailStart t ≤ n) :
    ‖t‖ / (n : ℝ) < 1 := by
  have hcut := Real.norm_lt_frequencyTailStart_cast t
  have hcast :
      ((Real.logarithmicPhaseFrequencyTailStart t : ℕ) : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hn
  exact Real.norm_div_nat_lt_one_of_norm_lt_nat t
    (lt_of_lt_of_le hcut hcast)

theorem Complex.logarithmicPhase_postCutoff_logRatio_nonneg
    {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) := by
  have hnCast : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hratioOne : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by
    exact (le_div_iff₀ hnCast).mpr
      (Eq.subst (motive := fun value : ℝ => value ≤ ((n + 1 : ℕ) : ℝ))
        (one_mul (n : ℝ)).symm
        (Nat.cast_le.mpr (Nat.le_succ n)))
  exact Real.log_nonneg hratioOne

theorem Complex.logarithmicPhase_postCutoff_logRatio_le_inv
    {n : ℕ} (hn : 0 < n) :
    Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) ≤ ((n : ℝ))⁻¹ :=
  Complex.logarithmicPhase_successive_log_ratio_upper_bound hn

theorem Complex.logarithmicPhase_postCutoff_increment_nonpos
    (t : ℝ) (ht : 0 ≤ t) {n : ℕ} (hn : 0 < n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n ≤ 0 := by
  have hformula :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hn
  have hlog := Complex.logarithmicPhase_postCutoff_logRatio_nonneg hn
  have hneg : -t ≤ 0 := neg_nonpos.mpr ht
  have hproduct := mul_nonpos_of_nonpos_of_nonneg hneg hlog
  exact Eq.subst (motive := fun value : ℝ => value ≤ 0)
    hformula.symm hproduct

theorem Complex.logarithmicPhase_postCutoff_increment_neg_one_lt
    (t : ℝ) (ht : 0 ≤ t) {n : ℕ}
    (hnTail : Real.logarithmicPhaseFrequencyTailStart t ≤ n) :
    -(1 : ℝ) <
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n := by
  have hnPos : 0 < n := lt_of_lt_of_le
    (Real.logarithmicPhaseFrequencyTailStart_pos t) hnTail
  have hformula :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hnPos
  have hlogUpper :=
    Complex.logarithmicPhase_postCutoff_logRatio_le_inv hnPos
  have htEq := Real.nonneg_parameter_eq_norm t ht
  have hscaled := mul_le_mul_of_nonneg_left hlogUpper ht
  have hmulInv : t * ((n : ℝ))⁻¹ = ‖t‖ / (n : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value * ((n : ℝ))⁻¹) htEq)
      (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
  have hratio := Real.postCutoff_norm_div_index_lt_one t hnTail
  have hpositive :
      t * Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) < 1 :=
    lt_of_le_of_lt
      (Eq.subst (motive := fun value : ℝ =>
        t * Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) ≤ value)
        hmulInv.symm hscaled)
      hratio
  have hnegative := neg_lt_neg hpositive
  have hnegProduct :
      -(t * Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ))) =
        -t * Real.log ((((n + 1 : ℕ) : ℝ)) / (n : ℝ)) :=
    neg_mul t _
  exact Eq.subst
    (motive := fun value : ℝ => -(1 : ℝ) < value)
    hformula.symm
    (Eq.subst (motive := fun value : ℝ => -(1 : ℝ) < value)
      hnegProduct.symm hnegative)

theorem Complex.logarithmicPhase_postCutoff_increment_mem_principal
    (t : ℝ) (ht : 0 ≤ t) {n : ℕ}
    (hnTail : Real.logarithmicPhaseFrequencyTailStart t ≤ n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n ∈
      Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  have hlowerOne :=
    Complex.logarithmicPhase_postCutoff_increment_neg_one_lt t ht hnTail
  have hminusPiLtMinusOne : -Real.pi < -(1 : ℝ) := by
    exact neg_lt_neg
      (lt_trans (Nat.one_lt_ofNat : (1 : ℝ) < 3) Real.pi_gt_three)
  have hlower := lt_trans hminusPiLtMinusOne hlowerOne
  have hnPos : 0 < n := lt_of_lt_of_le
    (Real.logarithmicPhaseFrequencyTailStart_pos t) hnTail
  have hnonpos :=
    Complex.logarithmicPhase_postCutoff_increment_nonpos t ht hnPos
  have hzeroLePi : (0 : ℝ) ≤ -Real.pi + 2 * Real.pi := by
    have hidentity : -Real.pi + 2 * Real.pi = Real.pi := by
      exact Eq.trans (neg_add_eq_sub Real.pi (2 * Real.pi))
        (Eq.trans (sub_eq_iff_eq_add.mpr (two_mul Real.pi).symm) rfl)
    exact Eq.subst (motive := fun value : ℝ => 0 ≤ value)
      hidentity.symm Real.pi_pos.le
  exact And.intro hlower (le_trans hnonpos hzeroLePi)

theorem Complex.logarithmicPhase_postCutoff_reducedIncrement_eq_raw
    (t : ℝ) (ht : 0 ≤ t) {n : ℕ}
    (hnTail : Real.logarithmicPhaseFrequencyTailStart t ≤ n) :
    Complex.realPhase_reducedIntegerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n :=
  Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal _
    (Complex.logarithmicPhase_postCutoff_increment_mem_principal
      t ht hnTail)

theorem Complex.logarithmicPhase_postCutoff_reducedIncrementMonotoneOn
    (t : ℝ) (ht : 0 ≤ t) {b : ℕ}
    (horder : Real.logarithmicPhaseFrequencyTailStart t ≤ b) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.logarithmicPhaseFrequencyTailStart t) b := by
  have hraw :=
    Complex.logarithmicPhaseRealPhase_integerIncrementMonotoneOn
      t ht
      (Nat.succ_le_of_lt
        (Real.logarithmicPhaseFrequencyTailStart_pos t))
  exact Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
    _ hraw
    (fun n hn =>
      Complex.logarithmicPhase_postCutoff_increment_mem_principal
        t ht (Finset.mem_Ico.mp hn).1)

end

end LFunctions
end Boundary
