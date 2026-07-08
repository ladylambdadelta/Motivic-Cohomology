import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PhaseDefs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBranch
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylTarget

/-!
# Logarithmic phase curvature owner

This file owns the small transport layer from the real scalar logarithmic phase
to the concrete complex samples `n ^ (-it)`.  The analytic packet estimate for
the real phase is a separate upstream theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-- A positive integer logarithmic-phase sample is the corresponding
real-phase exponential sample. -/
theorem Complex.logarithmicPhase_integer_sample_eq_realPhase_exp
    (t : ℝ)
    {n : ℕ}
    (hn_one : 1 ≤ n) :
    ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ)) := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hsample_function :
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n :=
    (Complex.logarithmicPhase_integer_sample_eq t hn_pos).symm
  have hfunction_phase :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n =
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
      t n
  exact Eq.trans hsample_function hfunction_phase

/-- A positive integer block of logarithmic-phase samples is the corresponding
real-phase exponential block. -/
theorem Complex.logarithmicPhase_integer_block_eq_realPhase_exp_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    (∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ)) := by
  exact Finset.sum_congr
    (Eq.refl (Finset.Icc a b))
    (fun n hn_mem =>
      have hn_one : 1 ≤ n :=
        le_trans ha (Finset.mem_Icc.mp hn_mem).1
      Complex.logarithmicPhase_integer_sample_eq_realPhase_exp
        (t := t)
        (n := n)
        hn_one)

/-- Transport a real-phase curvature block estimate to the concrete logarithmic
samples. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hreal :
      (‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖) ≤
        80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :
    (‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖) ≤
      80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) := by
  have hsample :
      (∑ n ∈ Finset.Icc a b,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) :=
    Complex.logarithmicPhase_integer_block_eq_realPhase_exp_block
      (t := t)
      (a := a)
      (b := b)
      (ha := ha)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)))
      hsample.symm
      hreal

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

/-- Concrete logarithmic curvature block estimate from all-integer
resonance-window avoidance and a Weyl-envelope target on every long positive
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
`π` gap bounds, positive-branch empty zero-centered resonance windows, and the
corresponding enlarged-envelope radicand target on every long positive
subblock. -/
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

end

end LFunctions
end Boundary
