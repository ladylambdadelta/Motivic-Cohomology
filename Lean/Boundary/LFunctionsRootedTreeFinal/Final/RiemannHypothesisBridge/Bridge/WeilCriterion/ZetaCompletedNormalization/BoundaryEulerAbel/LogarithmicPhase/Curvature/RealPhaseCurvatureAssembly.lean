import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseShortBlock
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicStationaryWindow
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicStationaryPacket
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDirectPoissonArithmetic

/-!
# Real-phase curvature branch assembly

This file owns the constructive finite branch split for the logarithmic
real-phase curvature estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Monotonicity bridge: the (correct, tighter) first-derivative endpoint norm
`(b+1)/‖t‖ + √(1+‖t‖)` is bounded by the (weaker, second-derivative-scaled)
`(b+1)/√‖t‖ + √(1+‖t‖)`, since `√‖t‖ ≤ ‖t‖` for `‖t‖ ≥ 1`. This lets the short
branches (which correctly produce the tighter bound) still satisfy the long
branch's corrected, weaker target. -/
theorem old_endpoint_norm_le_sqrt_norm (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℕ) :
    ((((b + 1 : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) ≤
      ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖) + Real.sqrt (1 + ‖t‖)) := by
  have hT_pos : (0 : ℝ) < ‖t‖ := lt_of_lt_of_le one_pos ht
  have hsqrtT_pos : (0 : ℝ) < Real.sqrt ‖t‖ := Real.sqrt_pos.mpr hT_pos
  have h1 : Real.sqrt 1 ≤ Real.sqrt ‖t‖ := Real.sqrt_le_sqrt ht
  have h2 : (1 : ℝ) ≤ Real.sqrt ‖t‖ := Real.sqrt_one ▸ h1
  have h3 : Real.sqrt ‖t‖ * 1 ≤ Real.sqrt ‖t‖ * Real.sqrt ‖t‖ :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
  have h4 : Real.sqrt ‖t‖ * Real.sqrt ‖t‖ = ‖t‖ := Real.mul_self_sqrt (le_of_lt hT_pos)
  have hsqrtT_le_T : Real.sqrt ‖t‖ ≤ ‖t‖ := by
    calc
      Real.sqrt ‖t‖ = Real.sqrt ‖t‖ * 1 := (mul_one _).symm
      _ ≤ Real.sqrt ‖t‖ * Real.sqrt ‖t‖ := h3
      _ = ‖t‖ := h4
  have hdiv_le : ((b + 1 : ℕ) : ℝ) / ‖t‖ ≤ ((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖ :=
    div_le_div_of_le_left (Nat.cast_nonneg (b + 1)) hsqrtT_pos hsqrtT_le_T
  exact add_le_add_right hdiv_le (Real.sqrt (1 + ‖t‖))

/-- Monotonicity bridge, scaled by the shared `80` factor. -/
theorem old_bound_le_sqrt_bound (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℕ) :
    80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) ≤
      80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖) + Real.sqrt (1 + ‖t‖)) :=
  mul_le_mul_of_nonneg_left (old_endpoint_norm_le_sqrt_norm t ht b) (Nat.cast_nonneg 80)

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
                      80 * ((((d + 1 : ℕ) : ℝ) / Real.sqrt ‖u‖ +
                        Real.sqrt (1 + ‖u‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  match Nat.eq_or_lt_of_le hab with
  | Or.inl hsingleton =>
      exact
        le_trans
          (Eq.subst
            (motive := fun right : ℕ =>
              ‖∑ n ∈ Finset.Icc a right,
                Complex.exp
                  (Complex.I *
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
              80 * ((((right + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
            hsingleton
            (Complex.logarithmicPhaseRealPhase_singleton_block_bound t ht a))
          (hsingleton ▸ old_bound_le_sqrt_bound t ht a)
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
              80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖ +
                Real.sqrt (1 + ‖t‖)))
          exact
            le_trans
              (Complex.logarithmicPhaseRealPhase_short_sqrt_block_bound
                t ht hab_succ hshort_sqrt)
              (old_bound_le_sqrt_bound t ht b)
      | Or.inl hlong_sqrt =>
          match lt_or_ge (((b + 1 : ℕ) : ℝ) / ‖t‖) L with
          | Or.inr hshort_endpoint =>
              show
                ‖∑ n ∈ Finset.Icc a b,
                  Complex.exp
                    (Complex.I *
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                        t n : ℂ))‖ ≤
                  80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖t‖ +
                    Real.sqrt (1 + ‖t‖)))
              exact
                le_trans
                  (Complex.logarithmicPhaseRealPhase_short_endpoint_block_bound
                    t ht hab_succ hshort_endpoint)
                  (old_bound_le_sqrt_bound t ht b)
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
                        80 * ((((b + 1 : ℕ) : ℝ) / Real.sqrt ‖-t‖ +
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
