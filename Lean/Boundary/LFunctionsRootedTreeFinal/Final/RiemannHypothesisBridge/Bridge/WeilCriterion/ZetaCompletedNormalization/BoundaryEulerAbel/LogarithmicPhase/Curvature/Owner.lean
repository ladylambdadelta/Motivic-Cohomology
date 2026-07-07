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
