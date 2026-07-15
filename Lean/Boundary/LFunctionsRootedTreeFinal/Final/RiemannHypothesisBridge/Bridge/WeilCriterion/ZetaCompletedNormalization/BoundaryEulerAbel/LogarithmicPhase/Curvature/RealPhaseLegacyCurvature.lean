import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLegacyConditionalAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBranch
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylArithmetic

namespace Boundary
namespace LFunctions

noncomputable section

/-! Compatibility curvature declarations moved out of the active RH owner. -/

/-! Canonical radicand compatibility chain. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_canonical_long_parameters_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (heta_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h ≤
                          Real.pi)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    Real.logarithmicPhaseRealPhase_longIncrementLo
                                    (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                    (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card :
                                      ℕ) : ℝ) *
                                  Real.logarithmicPhaseRealPhase_longWindowBudget ‖u‖ d h +
                                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      Real.logarithmicPhaseRealPhase_longIncrementLo
                                      (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                      (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card +
                                      1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        Real.logarithmicPhaseRealPhase_longIncrementLo
                                        (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                        Real.pi).card : ℕ) : ℝ) *
                                    (4 *
                                        ((Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹ +
                                          1) +
                                      4 * Real.pi *
                                        (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹))) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_refined_endpoint_spread_firstDerivative_radicand
      t ht ha hab
      (fun u _c d h => Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)
      (fun u _c d h => Real.logarithmicPhaseRealPhase_longRho ‖u‖ d h)
      (fun u _c d h => Real.logarithmicPhaseRealPhase_longWindowBudget ‖u‖ d h)
      (fun _u _c _d _h => Real.logarithmicPhaseRealPhase_longIncrementLo)
      (fun u c _d h => Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
      (fun u _hu_nonneg hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
          u hu_ht (b := d))
      heta_pi
      (fun u _hu_nonneg hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
          u hu_ht (b := d))
      (fun u _hu_nonneg _hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_majorizes
          ‖u‖ (b := d))
      (fun u hu_nonneg _hu_ht {c d} hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_mem_canonicalLongIncrementRange
          u hu_nonneg (a := c) (b := d) hc)
      (fun u hu_nonneg _hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longRho_rational_endpoint_spread
          u hu_nonneg (a := c) (b := d))
      (fun u _hu_nonneg hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
          u hu_ht (b := d))
      hrad

/-- Real-phase curvature block estimate with the canonical long-branch
all-integer resonance parameters; all local monotone-curvature hypotheses,
including `η ≤ π`, are discharged here. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_canonical_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    Real.logarithmicPhaseRealPhase_longIncrementLo
                                    (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                    (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card :
                                      ℕ) : ℝ) *
                                  Real.logarithmicPhaseRealPhase_longWindowBudget ‖u‖ d h +
                                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      Real.logarithmicPhaseRealPhase_longIncrementLo
                                      (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                      (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card +
                                      1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        Real.logarithmicPhaseRealPhase_longIncrementLo
                                        (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                        Real.pi).card : ℕ) : ℝ) *
                                    (4 *
                                        ((Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹ +
                                          1) +
                                      4 * Real.pi *
                                        (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹))) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_canonical_long_parameters_radicand
      t ht ha hab
      (fun u _hu_nonneg hu_ht {c d} _hc hd _hcd hlong_sqrt _hlong_endpoint =>
        Complex.logarithmicPhaseRealPhase_shiftRange_longEta_le_pi_of_sqrt_long
          u hu_ht hd hlong_sqrt)
      hrad

/-- Complex logarithmic curvature block estimate with the canonical
long-branch all-integer resonance parameters; only the finite canonical
radicand estimate remains as input. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_canonical_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    Real.logarithmicPhaseRealPhase_longIncrementLo
                                    (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                    (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card :
                                      ℕ) : ℝ) *
                                  Real.logarithmicPhaseRealPhase_longWindowBudget ‖u‖ d h +
                                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      Real.logarithmicPhaseRealPhase_longIncrementLo
                                      (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                      (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)).card +
                                      1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        Real.logarithmicPhaseRealPhase_longIncrementLo
                                        (Real.logarithmicPhaseRealPhase_longIncrementHi u c h)
                                        Real.pi).card : ℕ) : ℝ) *
                                    (4 *
                                        ((Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹ +
                                          1) +
                                      4 * Real.pi *
                                        (Real.logarithmicPhaseRealPhase_longEta ‖u‖ d h)⁻¹))) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hreal :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_canonical_radicand
      t ht ha hab hrad
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
      t ha hreal

/-- Concrete logarithmic curvature block estimate from the empty
zero-centered resonance-window radicand path. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_gap_pi_zero_resonanceWindow_empty_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hgap_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            Complex.realPhase_integerIncrement
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              n ≤ Real.pi)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((0 : ℝ) +
                                  (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h +
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_zero_resonanceWindow_empty_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (hlong_endpoint := hlong_endpoint)
        (hgap_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from scaled-reciprocal
no-winding, positive-branch empty zero-centered resonance windows, and the
corresponding enlarged-envelope radicand target on every long positive
subblock. -/

end

namespace Boundary
namespace LFunctions

noncomputable section

range-counting data, and the final Weyl radicand arithmetic. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_refined_endpoint_spread_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (lam rho W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (hlam :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h =
                          ‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ))
    (hlam_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h ≤ Real.pi)
    (hlam_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ lam u c d h)
    (hrho_pos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 < rho u c d h)
    (hW :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        (2 * lam u c d h) / rho u c d h + 1 ≤ W u c d h)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hrational :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ q r : ℕ,
                            Complex.realPhase_integerIncrementResonanceWindow
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h)
                                c (d - h) (2 * Real.pi * (k : ℝ))
                                (lam u c d h) =
                              Finset.Ico q r →
                            q < r - 1 →
                              rho u c d h * (((r - 1) - q : ℕ) : ℝ) ≤
                                ‖u‖ *
                                  (((h : ℝ) / (((q + 1) * (q + h) : ℕ) : ℝ)) -
                                    ((h : ℝ) /
                                      (((r - 1) * ((r - 1) + h + 1) : ℕ) : ℝ))))
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (lam u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (lam u c d h)).card + 1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        (lo u c d h) (hi u c d h) Real.pi).card : ℕ) : ℝ) *
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h :=
    fun u hu_nonneg hu_ht {c d} hc hd _hcd hlong_sqrt _hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
        u hu_ht hd hlong_sqrt
  have hpos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        1 ≤ h :=
    fun u _hu_nonneg _hu_ht {c d} _hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_shiftRange_pos u
  have hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h) :=
    fun u hu_nonneg _hu_ht {c d} hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_shiftRange_integerIncrementMonotone_of_nonneg
        u hu_nonneg hc
  have hwindow :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          k ∈
                            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                              u c d h (lam u c d h) →
                            ((Complex.realPhase_integerIncrementResonanceWindow
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              c (d - h) (2 * Real.pi * (k : ℝ))
                              (lam u c d h)).card : ℝ) ≤ W u c d h := by
    intro u hu_nonneg hu_ht c d hc hd hcd hlong_sqrt hlong_endpoint h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
        u hu_nonneg
        (a := c)
        (b := d)
        (lam := fun j => lam u c d j)
        (rho := fun j => rho u c d j)
        (W := fun j => W u c d j)
        hc
        (habh u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        (hinc_mono u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        (hlam_nonneg u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        (hrho_pos u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        (hW u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        (hrational u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd hlong_sqrt hlong_endpoint)
        h hh
  have hreal :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
      t ht ha hab lam W lo hi habh hpos hlam hlam_pi hrange hwindow
      hW_nonneg hinc_mono hrad
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
      t ha hreal

/-- Real-phase curvature block estimate from range-counted active
resonance-window bounds, monotone endpoint-spread window lengths, and
first-derivative all-principal-branch complement gaps on every long positive
subblock. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_refined_endpoint_spread_firstDerivative_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (eta rho W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (heta_pos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 < eta u c d h)
    (heta_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        eta u c d h ≤ Real.pi)
    (hrho_pos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 < rho u c d h)
    (hW :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        (2 * eta u c d h) / rho u c d h + 1 ≤ W u c d h)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hrational :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ q r : ℕ,
                            Complex.realPhase_integerIncrementResonanceWindow
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h)
                                c (d - h) (2 * Real.pi * (k : ℝ))
                                (eta u c d h) =
                              Finset.Ico q r →
                            q < r - 1 →
                              rho u c d h * (((r - 1) - q : ℕ) : ℝ) ≤
                                ‖u‖ *
                                  (((h : ℝ) / (((q + 1) * (q + h) : ℕ) : ℝ)) -
                                    ((h : ℝ) /
                                      (((r - 1) * ((r - 1) + h + 1) : ℕ) : ℝ))))
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (eta u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (eta u c d h)).card + 1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        (lo u c d h) (hi u c d h) Real.pi).card : ℕ) : ℝ) *
                                    (4 * ((eta u c d h)⁻¹ + 1) +
                                      4 * Real.pi * (eta u c d h)⁻¹))) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h :=
    fun u _hu_nonneg hu_ht {c d} _hc hd _hcd hlong_sqrt _hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
        u hu_ht hd hlong_sqrt
  have hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h) :=
    fun u hu_nonneg _hu_ht {c d} hc _hd _hcd _hlong_sqrt _hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_shiftRange_integerIncrementMonotone_of_nonneg
        u hu_nonneg hc
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_endpoint_spread_refinedPrincipalFirstDerivative_radicand
        u hu_nonneg hu_ht
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (eta := fun h => eta u c d h)
        (rho := fun h => rho u c d h)
        (W := fun h => W u c d h)
        (lo := fun h => lo u c d h)
        (hi := fun h => hi u c d h)
        (habh
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (heta_pos
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (heta_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrho_pos
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hW
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrange
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrational
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hW_nonneg
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hinc_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-! Scaled-reciprocal empty-window compatibility wrapper. -/+
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_scaled_reciprocal_zero_resonanceWindow_empty_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hscaled_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            u * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                              Real.pi)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((0 : ℝ) +
                                  (Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h +
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_zero_resonanceWindow_empty_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (hlong_endpoint := hlong_endpoint)
        (hscaled_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg


/-! Gap-pi resonance-window compatibility wrapper. -/+
/-- Concrete logarithmic curvature block estimate from direct shifted-increment
`π` gap bounds, zero-centered resonance-window avoidance, and an explicit
Weyl-envelope radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_gap_pi_resonanceWindow_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hgap_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            Complex.realPhase_integerIncrement
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              n ≤ Real.pi)
    (S : ℝ → ℕ → ℕ → ℕ → Finset ℕ)
    (hS :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ m : ℕ,
                          m ∈ S u c d h ↔
                            m ∈ Finset.Ico c (d - h) ∧
                              ‖Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  m -
                                (2 * Real.pi * (0 : ℝ))‖ <
                                (‖u‖ *
                                  ((((d + 1 : ℕ) : ℝ) *
                                    (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                  (h : ℝ)))
    (havoid :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            n ∉ S u c d h)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_resonanceWindow_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hgap_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (S u c d)
        (hS
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (havoid
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from direct shifted-increment


/-! Integer resonance-window compatibility wrappers. -/+
resonance-window avoidance and an explicit Weyl-envelope radicand target on
every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_integer_resonanceWindow_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hred_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_reducedIntegerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (S : ℝ → ℕ → ℕ → ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ m : ℕ,
                            m ∈ S u c d h k ↔
                              m ∈ Finset.Ico c (d - h) ∧
                                ‖Complex.realPhase_integerIncrement
                                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                      h)
                                    m -
                                  (2 * Real.pi * (k : ℝ))‖ <
                                  (‖u‖ *
                                    ((((d + 1 : ℕ) : ℝ) *
                                      (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                    (h : ℝ)))
    (havoid :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ n : ℕ,
                            n ∈ Finset.Ico c (d - h) →
                              n ∉ S u c d h k)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_resonanceWindow_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hred_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (S u c d)
        (hS
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (havoid
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from fixed integer branch
strips, all-integer resonance-window avoidance, and an explicit Weyl-envelope
radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_integer_strip_resonanceWindow_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (K : ℝ → ℕ → ℕ → ℕ → ℤ)
    (hstrip :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            Complex.realPhase_integerIncrement
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h)
                                n -
                                (2 * Real.pi * ((K u c d h : ℤ) : ℝ)) ∈
                              Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
    (S : ℝ → ℕ → ℕ → ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ m : ℕ,
                            m ∈ S u c d h k ↔
                              m ∈ Finset.Ico c (d - h) ∧
                                ‖Complex.realPhase_integerIncrement
                                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                      h)
                                    m -
                                  (2 * Real.pi * (k : ℝ))‖ <
                                  (‖u‖ *
                                    ((((d + 1 : ℕ) : ℝ) *
                                      (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                    (h : ℝ)))
    (havoid :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ n : ℕ,
                            n ∈ Finset.Ico c (d - h) →
                              n ∉ S u c d h k)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_strip_resonanceWindow_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (K u c d)
        (hstrip
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (S u c d)
        (hS
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (havoid
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg


/-! Scaled-reciprocal and gap-π separation compatibility wrappers. -/+
/-- Concrete logarithmic curvature block estimate from scaled reciprocal
no-winding arithmetic, zero-centered resonance-window avoidance, and an
explicit Weyl-envelope radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_scaled_reciprocal_resonanceWindow_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hscaled_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            u * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
                              Real.pi)
    (S : ℝ → ℕ → ℕ → ℕ → Finset ℕ)
    (hS :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ m : ℕ,
                          m ∈ S u c d h ↔
                            m ∈ Finset.Ico c (d - h) ∧
                              ‖Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  m -
                                (2 * Real.pi * (0 : ℝ))‖ <
                                (‖u‖ *
                                  ((((d + 1 : ℕ) : ℝ) *
                                    (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                  (h : ℝ)))
    (havoid :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            n ∉ S u c d h)
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaled_reciprocal_resonanceWindow_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hscaled_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (S u c d)
        (hS
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (havoid
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from direct shifted-increment
`π` gap bounds, direct shifted-increment separation, and an explicit
Weyl-envelope radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_gap_pi_sep_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hgap_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            Complex.realPhase_integerIncrement
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              n ≤ Real.pi)
    (hsep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementSeparatedOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h)
                          (‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ)))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_gap_pi_sep_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hgap_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hsep
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

`π` gap bounds, positive-branch empty zero-centered resonance windows, and the
corresponding enlarged-envelope radicand target on every long positive


/-! Range-counted and Weyl-envelope compatibility wrappers. -/+
/-- Concrete logarithmic curvature block estimate from the Weyl-envelope
radicand target and shifted-increment data on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_weylEnvelope_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hred_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_reducedIntegerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hsep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementSeparatedOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h)
                          (‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ)))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_weylEnvelope_radicand
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hinc_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hred_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hsep
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Real-phase curvature block estimate from range-counted active
resonance-window bounds and the refined all-principal-branch complement
radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (lam W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h)
    (hpos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        1 ≤ h)
    (hlam :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h =
                          ‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ))
    (hlam_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h ≤ Real.pi)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hwindow :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          k ∈
                            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                              u c d h (lam u c d h) →
                            ((Complex.realPhase_integerIncrementResonanceWindow
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              c (d - h) (2 * Real.pi * (k : ℝ))
                              (lam u c d h)).card : ℝ) ≤ W u c d h)
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (lam u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (lam u c d h)).card + 1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        (lo u c d h) (hi u c d h) Real.pi).card : ℕ) : ℝ) *
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
        u hu_nonneg hu_ht
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (lam := fun h => lam u c d h)
        (W := fun h => W u c d h)
        (lo := fun h => lo u c d h)
        (hi := fun h => hi u c d h)
        (habh
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hpos
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hlam
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hlam_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrange
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hwindow
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hW_nonneg
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hinc_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from range-counted active
resonance-window bounds and the refined all-principal-branch complement
radicand target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (lam W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h)
    (hpos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        1 ≤ h)
    (hlam :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h =
                          ‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ))
    (hlam_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h ≤ Real.pi)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hwindow :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          k ∈
                            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                              u c d h (lam u c d h) →
                            ((Complex.realPhase_integerIncrementResonanceWindow
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              c (d - h) (2 * Real.pi * (k : ℝ))
                              (lam u c d h)).card : ℝ) ≤ W u c d h)
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (lam u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (lam u c d h)).card + 1 : ℕ) *
                                      (Complex.realPhase_integerIncrementRangeActiveCenters
                                        (lo u c d h) (hi u c d h) Real.pi).card : ℕ) : ℝ) *
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hreal :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_refinedPrincipal_radicand
      t ht ha hab lam W lo hi habh hpos hlam hlam_pi hrange hwindow
      hW_nonneg hinc_mono hrad
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
      t ha hreal

/-- Concrete logarithmic curvature block estimate from range-counted active
resonance-window bounds and the corresponding explicit Weyl-envelope radicand
target on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (lam W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h)
    (hpos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        1 ≤ h)
    (hlam :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h =
                          ‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ))
    (hlam_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h ≤ Real.pi)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hwindow :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          k ∈
                            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                              u c d h (lam u c d h) →
                            ((Complex.realPhase_integerIncrementResonanceWindow
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              c (d - h) (2 * Real.pi * (k : ℝ))
                              (lam u c d h)).card : ℝ) ≤ W u c d h)
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hderiv_antitone :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        AntitoneOn
                          (fun x : ℝ =>
                            ‖deriv
                            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              h) x‖)
                          (Set.Icc (c : ℝ) (((d - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ x : ℝ,
                          x ∈ Set.Icc (c : ℝ) (((d - h) + 1 : ℕ) : ℝ) →
                            ‖u‖ *
                                ((((d + 1 : ℕ) : ℝ) *
                                  (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                (h : ℝ) ≤
                              ‖deriv
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h) x‖)
    (hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hred_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_reducedIntegerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (lam u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  ((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (lam u c d h)).card + 1 : ℕ) : ℝ) *
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_window_radicand
        u hu_nonneg hu_ht
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (lam := fun h => lam u c d h)
        (W := fun h => W u c d h)
        (lo := fun h => lo u c d h)
        (hi := fun h => hi u c d h)
        (habh
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hpos
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hlam
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hlam_pi
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrange
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hwindow
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hW_nonneg
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hderiv_antitone
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hderiv_lower
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hinc_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hred_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrad
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from the range-counted
all-integer resonance decomposition, with integer-centered window lengths
discharged by the monotone endpoint-spread estimate on every long positive
subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_endpoint_spread_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (lam rho W lo hi : ℝ → ℕ → ℕ → ℕ → ℝ)
    (habh :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        c ≤ d - h)
    (hpos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        1 ≤ h)
    (hlam :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h =
                          ‖u‖ *
                            ((((d + 1 : ℕ) : ℝ) *
                              (((d + 1 : ℕ) : ℝ)))⁻¹) *
                            (h : ℝ))
    (hlam_pi :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        lam u c d h ≤ Real.pi)
    (hlam_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ lam u c d h)
    (hrho_pos :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 < rho u c d h)
    (hW :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        (2 * lam u c d h) / rho u c d h + 1 ≤ W u c d h)
    (hrange :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ n : ℕ,
                          n ∈ Finset.Ico c (d - h) →
                            lo u c d h ≤
                                Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ∧
                              Complex.realPhase_integerIncrement
                                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                    h)
                                  n ≤ hi u c d h)
    (hrational :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ q r : ℕ,
                            Complex.realPhase_integerIncrementResonanceWindow
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h)
                                c (d - h) (2 * Real.pi * (k : ℝ))
                                (lam u c d h) =
                              Finset.Ico q r →
                            q < r - 1 →
                              rho u c d h * (((r - 1) - q : ℕ) : ℝ) ≤
                                ‖u‖ *
                                  (((h : ℝ) / (((q + 1) * (q + h) : ℕ) : ℝ)) -
                                    ((h : ℝ) /
                                      (((r - 1) * ((r - 1) + h + 1) : ℕ) : ℝ))))
    (hW_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        0 ≤ W u c d h)
    (hderiv_antitone :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        AntitoneOn
                          (fun x : ℝ =>
                            ‖deriv
                            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              h) x‖)
                          (Set.Icc (c : ℝ) (((d - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ x : ℝ,
                          x ∈ Set.Icc (c : ℝ) (((d - h) + 1 : ℕ) : ℝ) →
                            ‖u‖ *
                                ((((d + 1 : ℕ) : ℝ) *
                                  (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                (h : ℝ) ≤
                              ‖deriv
                                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                  h) x‖)
    (hinc_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_integerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hred_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_reducedIntegerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (hrad :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ((Real.secondDerivativeVdc_blockLength c d) +
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℝ)) *
                        (((Real.secondDerivativeVdc_blockLength c d) +
                            2 *
                              (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                                (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                                (((((Complex.realPhase_integerIncrementRangeActiveCenters
                                    (lo u c d h) (hi u c d h)
                                    (lam u c d h)).card : ℕ) : ℝ) *
                                  W u c d h +
                                  ((((Complex.realPhase_integerIncrementRangeActiveCenters
                                      (lo u c d h) (hi u c d h)
                                      (lam u c d h)).card + 1 : ℕ) : ℝ) *
                                    Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h)) +
                                  1))) *
                          (((Real.secondDerivativeVdc_weylShiftLength ‖u‖ : ℕ) : ℝ)⁻¹)) ≤
                      (80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hwindow :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          k ∈
                            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                              u c d h (lam u c d h) →
                            ((Complex.realPhase_integerIncrementResonanceWindow
                              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                h)
                              c (d - h) (2 * Real.pi * (k : ℝ))
                              (lam u c d h)).card : ℝ) ≤ W u c d h := by
    intro u hu_nonneg hu_ht c d hc hd hcd_strict hlong_sqrt hlong_endpoint h hh
    exact
      Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
        u hu_nonneg
        (a := c)
        (b := d)
        (lam := fun j => lam u c d j)
        (rho := fun j => rho u c d j)
        (W := fun j => W u c d j)
        hc
        (habh u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hinc_mono u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hlam_nonneg u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrho_pos u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hW u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hrational u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        h hh
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_rangeCounted_activeCenter_window_radicand
      t ht ha hab lam W lo hi habh hpos hlam hlam_pi hrange hwindow
      hW_nonneg hderiv_antitone hderiv_lower hinc_mono hred_mono hrad



/-! Legacy witness-heavy Owner wrappers. -/+
/-- Assemble the concrete logarithmic samples from the real-phase curvature
branch split and a positive-parameter long-branch theorem. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hreal :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
      t ha hreal

/-- Concrete logarithmic curvature block estimate from the stationary-family
long branch and endpoint reciprocal-scale cut bounds. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_stationaryFamily_scaleCut_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary_family :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d
                        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets
                          u c d),
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      10 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖))))
    (hleftScale :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((Finset.Icc c d).filter
                      (fun n : ℕ =>
                        ‖u‖ / (c : ℝ) - (1 / 2 : ℝ) < ‖u‖ / (n : ℝ))).card :
                        ℝ) ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖))))
    (hfarScale :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((Finset.Icc c d).filter
                      (fun n : ℕ =>
                        ‖u‖ / (n : ℝ) <
                          ‖u‖ / (((d + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card :
                        ℝ) ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamily_scaleCut_bounds
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hstationary_family
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hleftScale
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hfarScale
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from the stationary packet
budget and endpoint reciprocal-scale cut bounds on every long positive
subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_scaleCut_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))))
    (hleftScale :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((Finset.Icc c d).filter
                      (fun n : ℕ =>
                        ‖u‖ / (c : ℝ) - (1 / 2 : ℝ) < ‖u‖ / (n : ℝ))).card :
                        ℝ) ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖))))
    (hfarScale :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((Finset.Icc c d).filter
                      (fun n : ℕ =>
                        ‖u‖ / (n : ℝ) <
                          ‖u‖ / (((d + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card :
                        ℝ) ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_scaleCut_bounds
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hstationary
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hleftScale
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hfarScale
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from closed stationary and
endpoint packet-contribution budgets on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_stationary_endpoint_budgets
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))))
    (hendpoint :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      60 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationary_endpoint_budgets
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (hlong_endpoint := hlong_endpoint)
        (hstationary
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hendpoint
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from closed stationary and
three closed endpoint-tail packet budgets on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_tail_budgets
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))))
    (hleft :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))))
    (hright :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets u c d,
                      Complex.realPhase_secondDerivative_vdc_packetSum
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d m‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_tail_budgets
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hstationary
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hleft
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hright
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from uniform closed
subinterval twentieth-budget estimates on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hIcc :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {q r : ℕ},
                      c ≤ q →
                        q ≤ r →
                          r ≤ d →
                            ‖∑ n ∈ Finset.Icc q r,
                              Complex.exp
                                (Complex.I *
                                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                                    u n : ℂ))‖ ≤
                              20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                                Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_Icc_bounds
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (fun {q r} hcq hqr hrd =>
          hIcc
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcq hqr hrd)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from the refined
all-integer resonance decomposition.  The automatic long-branch shift
bookkeeping and shifted-increment monotonicity are discharged here; the
remaining hypotheses are exactly the endpoint-spread window arithmetic, the
subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_integer_resonanceWindow
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hred_mono :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        Complex.realPhase_reducedIntegerIncrementMonotoneOn
                          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            h)
                          c (d - h))
    (S : ℝ → ℕ → ℕ → ℕ → ℤ → Finset ℕ)
    (hS :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ m : ℕ,
                            m ∈ S u c d h k ↔
                              m ∈ Finset.Ico c (d - h) ∧
                                ‖Complex.realPhase_integerIncrement
                                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                                      h)
                                    m -
                                  (2 * Real.pi * (k : ℝ))‖ <
                                  (‖u‖ *
                                    ((((d + 1 : ℕ) : ℝ) *
                                      (((d + 1 : ℕ) : ℝ)))⁻¹) *
                                    (h : ℝ)))
    (havoid :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ h : ℕ,
                      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖) →
                        ∀ k : ℤ,
                          ∀ n : ℕ,
                            n ∈ Finset.Ico c (d - h) →
                              n ∉ S u c d h k)
    (hweyl_target :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    Real.secondDerivativeVdc_weylEnvelopeMajorant c d
                        (Real.secondDerivativeVdc_weylShiftLength ‖u‖)
                        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                          (Real.secondDerivativeVdc_weylShiftLength ‖u‖),
                          Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖u‖ d h) ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_integer_resonanceWindow
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hred_mono
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (S u c d)
        (hS
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (havoid
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (hweyl_target
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from all-integer
/-- Concrete logarithmic curvature block estimate from stationary-family
control and endpoint first-derivative data on every long positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_stationaryFamily_endpoint_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary_family :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d
                        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets
                          u c d),
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      10 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖))))
    (hleft_reduced :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {r : ℕ},
                      c ≤ r →
                        r ≤ d →
                          Complex.realPhase_reducedIntegerIncrementMonotoneOn
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            c r)
    (hleft_sep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {r : ℕ},
                      c ≤ r →
                        r ≤ d →
                          Complex.realPhase_integerIncrementSeparatedOn
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            c r
                            (‖u‖ / ((r + 1 : ℕ) : ℝ)))
    (hfar_reduced :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {q r : ℕ},
                      c ≤ q →
                        q ≤ r →
                          r ≤ d →
                            Complex.realPhase_reducedIntegerIncrementMonotoneOn
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              q r)
    (hfar_sep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {q r : ℕ},
                      c ≤ q →
                        q ≤ r →
                          r ≤ d →
                            Complex.realPhase_integerIncrementSeparatedOn
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              q r
                              (‖u‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamily_endpoint_firstDerivative_data
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hstationary_family
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (fun {r} hcr hrd =>
          hleft_reduced
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcr hrd)
        (fun {r} hcr hrd =>
          hleft_sep
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcr hrd)
        (fun {q r} hcq hqr hrd =>
          hfar_reduced
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcq hqr hrd)
        (fun {q r} hcq hqr hrd =>
          hfar_sep
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcq hqr hrd)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Concrete logarithmic curvature block estimate from twentieth-budget
stationary-family control and endpoint first-derivative data on every long
positive subblock. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_stationaryFamilyTwenty_endpoint_firstDerivative_data
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary_family :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
                        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                        c d
                        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets
                          u c d),
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      20 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ + Real.sqrt (1 + ‖u‖))))
    (hleft_reduced :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {r : ℕ},
                      c ≤ r →
                        r ≤ d →
                          Complex.realPhase_reducedIntegerIncrementMonotoneOn
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            c r)
    (hleft_sep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {r : ℕ},
                      c ≤ r →
                        r ≤ d →
                          Complex.realPhase_integerIncrementSeparatedOn
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                            c r
                            (‖u‖ / ((r + 1 : ℕ) : ℝ)))
    (hfar_reduced :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {q r : ℕ},
                      c ≤ q →
                        q ≤ r →
                          r ≤ d →
                            Complex.realPhase_reducedIntegerIncrementMonotoneOn
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              q r)
    (hfar_sep :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ∀ {q r : ℕ},
                      c ≤ q →
                        q ≤ r →
                          r ≤ d →
                            Complex.realPhase_integerIncrementSeparatedOn
                              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase u)
                              q r
                              (‖u‖ / ((r + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / ‖u‖ +
                        Real.sqrt (1 + ‖u‖))) :=
    fun u hu_nonneg hu_ht {c d} hc hd hcd_strict hlong_sqrt hlong_endpoint =>
      Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_stationaryFamilyTwenty_endpoint_firstDerivative_data
        (t := u)
        (ht_nonneg := hu_nonneg)
        (ht := hu_ht)
        (a := c)
        (b := d)
        (ha := hc)
        (hab := hd)
        (_hab_strict := hcd_strict)
        (_hlong_sqrt := hlong_sqrt)
        (_hlong_endpoint := hlong_endpoint)
        (hstationary_family
          u hu_nonneg hu_ht (c := c) (d := d)
          hc hd hcd_strict hlong_sqrt hlong_endpoint)
        (fun {r} hcr hrd =>
          hleft_reduced
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcr hrd)
        (fun {r} hcr hrd =>
          hleft_sep
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcr hrd)
        (fun {q r} hcq hqr hrd =>
          hfar_reduced
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcq hqr hrd)
        (fun {q r} hcq hqr hrd =>
          hfar_sep
            u hu_nonneg hu_ht (c := c) (d := d)
            hc hd hcd_strict hlong_sqrt hlong_endpoint hcq hqr hrd)
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg

/-- Unconditional positive long-branch real-phase curvature estimate.

The public owner theorem consumes an explicit long-branch owner bound and
then performs only the sign-symmetry branch assembly. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_nonneg :
      ∀ u : ℝ,
        0 ≤ u →
          1 ≤ ‖u‖ →
            ∀ {c d : ℕ},
              1 ≤ c →
                c ≤ d →
                  c < d →
                    Real.sqrt (1 + ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    (((d + 1 : ℕ) : ℝ) / ‖u‖) <
                      (((d + 1 : ℕ) : ℝ) - (c : ℝ)) →
                    ‖∑ n ∈ Finset.Icc c d,
                      Complex.exp
                        (Complex.I *
                          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                            u n : ℂ))‖ ≤
                      80 * ((((d + 1 : ℕ) : ℝ) / Real.sqrt ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_long_nonneg
      t ht ha hab hlong_nonneg



/-- End of the compatibility curvature limb. -/

end

end LFunctions
end Boundary
