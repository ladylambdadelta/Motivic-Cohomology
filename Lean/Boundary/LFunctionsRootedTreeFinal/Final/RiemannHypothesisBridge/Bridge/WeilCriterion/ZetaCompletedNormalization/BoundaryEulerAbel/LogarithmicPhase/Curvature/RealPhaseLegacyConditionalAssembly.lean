import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseShortBlock

/-!
# Legacy conditional curvature assembly

This file preserves the callback-based branch assembler solely for deprecated
radicand and witness-driven consumers. The active RH cone uses the comparable,
witness-free assembly in RealPhaseCurvatureAssembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

noncomputable section

open scoped Topology

/-- Assemble the real-phase curvature block estimate from the short branches
and the positive-parameter long branch. -/
theorem Complex.logarithmicPhaseRealPhase_curvature_integer_block_bound_of_long_nonneg
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
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  match Nat.eq_or_lt_of_le hab with
  | Or.inl hsingleton =>
      exact
        Eq.subst
            (motive := fun right : ℕ =>
              ‖∑ n ∈ Finset.Icc a right,
                Complex.exp
                  (Complex.I *
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((right + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
            hsingleton
            (Complex.logarithmicPhaseRealPhase_singleton_block_bound t ht a)
  | Or.inr hab_strict =>
      have hab_succ : a ≤ b + 1 :=
        Nat.le_trans hab (Nat.le_succ b)
      let L : ℝ := (((b + 1 : ℕ) : ℝ) - (a : ℝ))
      match lt_or_ge (Real.sqrt (1 + ‖t‖)) L with
      | Or.inr hshort_sqrt =>
          show
            ‖∑ n ∈ Finset.Icc a b,
              Complex.exp
                (Complex.I *
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
                Real.sqrt (1 + ‖t‖)))
          exact
            Complex.logarithmicPhaseRealPhase_short_sqrt_block_bound
              t ht hab_succ hshort_sqrt
      | Or.inl hlong_sqrt =>
          match lt_or_ge (((b + 1 : ℕ) : ℝ) / ‖t‖) L with
          | Or.inr hshort_endpoint =>
              show
                ‖∑ n ∈ Finset.Icc a b,
                  Complex.exp
                    (Complex.I *
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                        t n : ℂ))‖ ≤
                  80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
                    Real.sqrt (1 + ‖t‖)))
              exact
                Complex.logarithmicPhaseRealPhase_short_endpoint_block_bound
                  t ht hab_succ hshort_endpoint
          | Or.inl hlong_endpoint =>
              match le_total (0 : ℝ) t with
              | Or.inl ht_nonneg =>
                  exact
                    hlong_nonneg t ht_nonneg ht ha hab hab_strict
                      hlong_sqrt hlong_endpoint
              | Or.inr ht_nonpos =>
                  have hneg_nonneg : 0 ≤ -t :=
                    neg_nonneg.mpr ht_nonpos
                  have hneg_norm : ‖-t‖ = ‖t‖ :=
                    norm_neg t
                  have hneg_ht : 1 ≤ ‖-t‖ :=
                    Eq.subst
                      (motive := fun r : ℝ => 1 ≤ r)
                      hneg_norm.symm
                      ht
                  have hneg_bound :
                      ‖∑ n ∈ Finset.Icc a b,
                        Complex.exp
                          (Complex.I *
                            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                              (-t) n : ℂ))‖ ≤
                        80 * ((((b + 1 : ℕ) : ℝ) / ‖-t‖ +
                          Real.sqrt (1 + ‖-t‖))) :=
                    hlong_nonneg (-t) hneg_nonneg hneg_ht ha hab hab_strict
                      (Eq.subst
                        (motive := fun r : ℝ =>
                          Real.sqrt (1 + r) <
                            (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
                        hneg_norm.symm
                        hlong_sqrt)
                      (Eq.subst
                        (motive := fun r : ℝ =>
                          (((b + 1 : ℕ) : ℝ) / r) <
                            (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
                        hneg_norm.symm
                        hlong_endpoint)
                  exact
                    Complex.logarithmicPhaseRealPhase_block_bound_of_neg_parameter_bound
                      t hneg_bound

end

end LFunctions
end Boundary

