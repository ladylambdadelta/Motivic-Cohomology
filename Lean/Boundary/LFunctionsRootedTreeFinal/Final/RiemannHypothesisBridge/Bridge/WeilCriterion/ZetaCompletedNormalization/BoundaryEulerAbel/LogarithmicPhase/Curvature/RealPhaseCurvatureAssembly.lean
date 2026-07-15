import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseShortBlock
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUnconditionalLong

/-!
# Real-phase curvature branch assembly

This file owns the constructive finite branch split for the logarithmic
real-phase curvature estimate.
-/

namespace Boundary
namespace LFunctions


theorem Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_sqrt_target
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  exact Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional
    t ht_nonneg ht a b hgeometry

theorem Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_of_explicit_geometry_sqrt_target
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstrict : a < b)
    (hsqrt : Real.sqrt (1 + ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hendpoint : (((b + 1 : ℕ) : ℝ) / ‖t‖) <
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hcomparable : b + 1 ≤ 2 * a) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  have hgeometry := Real.logarithmicPhaseLongBranchGeometry_mk
    t a b ha hab hstrict hsqrt hendpoint hcomparable
  exact Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_sqrt_target
    t ht_nonneg ht a b hgeometry

theorem Complex.logarithmicPhaseRealPhase_comparable_curvature_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hcomparable : b + 1 ≤ 2 * a) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  match Nat.eq_or_lt_of_le hab with
  | Or.inl hsingleton =>
      have hsingle := Complex.logarithmicPhaseRealPhase_singleton_block_bound
        t ht a
      exact Eq.subst
        (motive := fun right : ℕ =>
          ‖∑ n ∈ Finset.Icc a right,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            80 * ((((right + 1 : ℕ) : ℝ) / ‖t‖ +
              Real.sqrt (1 + ‖t‖))))
        hsingleton hsingle
  | Or.inr hstrict =>
      let L : ℝ := (((b + 1 : ℕ) : ℝ) - (a : ℝ))
      have habSucc : a ≤ b + 1 := Nat.le_trans hab (Nat.le_succ b)
      match lt_or_ge (Real.sqrt (1 + ‖t‖)) L with
      | Or.inr hshortSqrt =>
          exact Complex.logarithmicPhaseRealPhase_short_sqrt_block_bound
            t ht habSucc hshortSqrt
      | Or.inl hlongSqrt =>
          match lt_or_ge (((b + 1 : ℕ) : ℝ) / ‖t‖) L with
          | Or.inr hshortEndpoint =>
              exact Complex.logarithmicPhaseRealPhase_short_endpoint_block_bound
                t ht habSucc hshortEndpoint
          | Or.inl hlongEndpoint =>
              match le_total (0 : ℝ) t with
              | Or.inl htNonneg =>
                  exact
                    Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_of_explicit_geometry_sqrt_target
                      t htNonneg ht a b ha hab hstrict hlongSqrt
                      hlongEndpoint hcomparable
              | Or.inr htNonpos =>
                  have hnegNonneg : 0 ≤ -t := neg_nonneg.mpr htNonpos
                  have hnorm : ‖-t‖ = ‖t‖ := norm_neg t
                  have hnegHt : 1 ≤ ‖-t‖ :=
                    Eq.subst (motive := fun value : ℝ => 1 ≤ value)
                      hnorm.symm ht
                  have hnegSqrt : Real.sqrt (1 + ‖-t‖) < L :=
                    Eq.subst
                      (motive := fun value : ℝ => Real.sqrt (1 + value) < L)
                      hnorm.symm hlongSqrt
                  have hnegEndpoint :
                      (((b + 1 : ℕ) : ℝ) / ‖-t‖) < L :=
                    Eq.subst
                      (motive := fun value : ℝ =>
                        (((b + 1 : ℕ) : ℝ) / value) < L)
                      hnorm.symm hlongEndpoint
                  have hnegBound :=
                    Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional_of_explicit_geometry_sqrt_target
                      (-t) hnegNonneg hnegHt a b ha hab hstrict hnegSqrt
                      hnegEndpoint hcomparable
                  exact
                    Complex.logarithmicPhaseRealPhase_block_bound_of_neg_parameter_bound
                      t hnegBound

end LFunctions
end Boundary
