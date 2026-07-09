import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcVariation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveParameters
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Long-branch chord Abel owner facts

This file owns the non-principal-branch all-integer Abel path for one
long-branch shifted correlation.  The analytic inputs are the endpoint and
variation estimates for the canonical inverse geometric denominator.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace Complex

/-- The shifted logarithmic real phase for one Weyl shift. -/
abbrev logarithmicPhaseRealPhase_shiftedDifferencePhase
    (t : ℝ)
    (h : ℕ) : ℝ → ℝ :=
  Complex.realPhase_secondDerivative_vdc_shiftedDifference
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    h

/-- Canonical long-branch chord endpoint budget for one shifted correlation. -/
abbrev logarithmicPhaseRealPhase_longChordEndpointBudget
    (t : ℝ)
    (b h : ℕ) : ℝ :=
  4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1)

/-- Canonical long-branch chord variation budget for one shifted correlation. -/
abbrev logarithmicPhaseRealPhase_longChordVariationBudget
    (t : ℝ)
    (b h : ℕ) : ℝ :=
  4 * Real.pi *
    (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹

/-- Endpoint control for the canonical inverse geometric denominator on a long
all-integer reduced-arc block. -/
theorem logarithmicPhaseRealPhase_shiftedDifference_inverseDenominator_endpoint_le_longBudget
    (t : ℝ)
    (h a b : ℕ)
    (ha : 1 ≤ a)
    (habh_strict : a < b - h)
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)
    (hred :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h)
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)) :
    ‖Complex.realPhase_inverseGeometricDenominator
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h) a‖ +
        ‖Complex.realPhase_inverseGeometricDenominator
          (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
          ((b - h) - 1)‖ ≤
      Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h := by
  exact
    Complex.realPhase_allIntegerMonotoneSeparated_inverseGeometricDenominator_endpoint_bound
      (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
      ha habh_strict heta_pos hsep

/-- Total variation control for the canonical inverse geometric denominator on a long
all-integer reduced-arc block. -/
theorem logarithmicPhaseRealPhase_shiftedDifference_inverseDenominator_variation_le_longBudget
    (t : ℝ)
    (h a b : ℕ)
    (habh_strict : a < b - h)
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)
    (hred :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h)
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)) :
    (∑ n ∈ Finset.Ico (a + 1) (b - h),
      ‖Complex.realPhase_inverseGeometricDenominator
          (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h) n -
        Complex.realPhase_inverseGeometricDenominator
          (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
          (n - 1)‖) ≤
      Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h := by
  let φ : ℝ → ℝ :=
    Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h
  let d : ℕ := b - h
  have hd_mem : d ∈ Finset.Icc a d :=
    Finset.mem_Icc.mpr ⟨le_of_lt habh_strict, le_rfl⟩
  have hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a d →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ := by
    intro n hn
    unfold φ
    exact
      Complex.realPhase_geometricDenominator_inv_norm_bound
        heta_pos
        (hsep n hn)
  have hvariation_Ioo :
      (∑ n ∈ Finset.Ioo a d,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
        4 * Real.pi *
          (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ := by
    unfold φ
    exact
      Complex.realPhase_reducedMonotoneSeparated_inverseGeometricDenominator_variation_bound
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        habh_strict
        hd_mem
        heta_pos
        hred
        hsep
        hden
  have hIoo :
      Finset.Ioo a d = Finset.Ico (a + 1) d :=
    Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase a d
  have hvariation_Ico :
      (∑ n ∈ Finset.Ico (a + 1) d,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
        4 * Real.pi *
          (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
    Eq.subst
      (motive := fun S : Finset ℕ =>
        (∑ n ∈ S,
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
          4 * Real.pi *
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹)
      hIoo
      hvariation_Ioo
  exact hvariation_Ico

/-- One shifted correlation is controlled by the global half-open chord Abel
variation estimate. -/
theorem logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_longChordAbelBudget
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (habh_strict : a < b - h)
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)
    (hred :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h)
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
        Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 := by
  let φ : ℝ → ℝ :=
    Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h
  have hico :
      ‖∑ n ∈ Finset.Ico a (b - h),
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
          Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h :=
    Complex.realPhase_Ico_sum_norm_le_allIntegerAbelVariation
      φ
      heta_pos
      hsep
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_inverseDenominator_endpoint_le_longBudget
        t h a b ha habh_strict heta_pos hred hsep)
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_inverseDenominator_variation_le_longBudget
        t h a b habh_strict heta_pos hred hsep)
  have hterminal :
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
        ‖∑ n ∈ Finset.Ico a (b - h),
          Complex.exp (Complex.I * (φ n : ℂ))‖ + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
      t habh
  exact le_trans hterminal (add_le_add_right hico 1)

/-- The long chord endpoint budget is nonnegative. -/
theorem logarithmicPhaseRealPhase_longChordEndpointBudget_nonneg
    (t : ℝ)
    {b h : ℕ}
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) :
    0 ≤ Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h := by
  have heta_inv_nonneg :
      0 ≤ (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
    inv_nonneg.mpr (le_of_lt heta_pos)
  have hinner_nonneg :
      0 ≤ (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1 :=
    add_nonneg heta_inv_nonneg zero_le_one
  exact mul_nonneg zero_le_four hinner_nonneg

/-- The long chord variation budget is nonnegative. -/
theorem logarithmicPhaseRealPhase_longChordVariationBudget_nonneg
    (t : ℝ)
    {b h : ℕ}
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) :
    0 ≤ Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h := by
  have heta_inv_nonneg :
      0 ≤ (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
    inv_nonneg.mpr (le_of_lt heta_pos)
  have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
    mul_nonneg zero_le_four Real.pi_nonneg
  exact mul_nonneg hfour_pi_nonneg heta_inv_nonneg

/-- One shifted correlation is controlled by the long chord-Abel budget, with
the endpoint-degenerate half-open block handled separately. -/
theorem logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_longChordAbelBudget_of_le
    (t : ℝ)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (heta_pos : 0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)
    (hred :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
        a (b - h)
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)) :
    ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
      Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
        Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 := by
  match lt_or_eq_of_le habh with
  | Or.inl habh_strict =>
      exact
        Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_longChordAbelBudget
          t ha habh habh_strict heta_pos hred hsep
  | Or.inr habh_eq =>
      let φ : ℝ → ℝ :=
        Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h
      have hterminal :
          ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
            ‖∑ n ∈ Finset.Ico a (b - h),
              Complex.exp (Complex.I * (φ n : ℂ))‖ + 1 :=
        Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
          t habh
      have hIco_empty : Finset.Ico a (b - h) = (∅ : Finset ℕ) :=
        Finset.Ico_eq_empty
          (Eq.subst
            (motive := fun right : ℕ => ¬ a < right)
            habh_eq
            (not_lt_of_ge (Nat.le_refl a)))
      have hsum_empty :
          (∑ n ∈ Finset.Ico a (b - h),
              Complex.exp (Complex.I * (φ n : ℂ))) = 0 := by
        exact Eq.trans
          (congrArg
            (fun S : Finset ℕ =>
              ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
            hIco_empty)
          Finset.sum_empty
      have hterminal_one :
          ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
            1 :=
        le_trans hterminal
          (le_of_eq
            (Eq.trans
              (congrArg
                (fun z : ℂ => ‖z‖ + 1)
                hsum_empty)
              (congrArg (fun r : ℝ => r + 1) norm_zero)))
      have hbudget_nonneg :
          0 ≤
            Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
              Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h :=
        add_nonneg
          (Complex.logarithmicPhaseRealPhase_longChordEndpointBudget_nonneg
            t heta_pos)
          (Complex.logarithmicPhaseRealPhase_longChordVariationBudget_nonneg
            t heta_pos)
      exact le_trans hterminal_one (le_add_of_nonneg_left hbudget_nonneg)

end Complex

end

end LFunctions
end Boundary
