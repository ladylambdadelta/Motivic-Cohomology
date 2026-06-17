import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail.Algebra

/-!
# Abstract Abel damping for boundary tails

This file owns the generic finite Abel-transform and positive damping lemmas
used before specializing to the boundary-line zeta tail.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Finite Stieltjes/Abel control for a bounded family of tails under a
positive decreasing weight.

This is the abstract finite form of the convex-combination argument: summation
by parts rewrites the weighted tail as a nonnegative linear combination of
undamped finite tails, with total mass bounded by the initial weight. -/
theorem Complex.zeroExtended_tail_prefix_sum_eq_Ioc
    {a : ℕ → ℂ}
    (N k : ℕ) :
    (∑ n ∈ Finset.range (k + 1), if N < n then a n else 0) =
      ∑ n ∈ Finset.Ioc N k, a n := by
  have hfilter :
      (Finset.range (k + 1)).filter (fun n : ℕ => N < n) =
        Finset.Ioc N k := by
    ext n
    constructor
    · intro hn
      have hn_range : n < k + 1 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      have hNn : N < n :=
        (Finset.mem_filter.mp hn).2
      exact Finset.mem_Ioc.mpr ⟨hNn, Nat.le_of_lt_succ hn_range⟩
    · intro hn
      have hNn : N < n := (Finset.mem_Ioc.mp hn).1
      have hnk : n ≤ k := (Finset.mem_Ioc.mp hn).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnk), hNn⟩
  calc
    (∑ n ∈ Finset.range (k + 1), if N < n then a n else 0) =
        ∑ n ∈ (Finset.range (k + 1)).filter (fun n : ℕ => N < n), a n :=
      Finset.sum_filter
    _ = ∑ n ∈ Finset.Ioc N k, a n := by
      exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, a n) hfilter

theorem Complex.finite_weighted_tail_abel_identity
    {a : ℕ → ℂ}
    {w : ℕ → ℝ}
    (N M : ℕ)
    (hNM : N < M) :
    (∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ)) =
      (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) +
        ∑ k ∈ Finset.Ioc N (M - 1),
          ((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ n ∈ Finset.Ioc N k, a n) := by
  /-
  This is the finite Abel transform for the zero-extended tail sequence.
  It is the owner identity needed by the norm estimate below.
  -/
  let b : ℕ → ℂ := fun n : ℕ => if N < n then a n else 0
  have hparts :=
    Finset.sum_Ioc_by_parts
      (fun n : ℕ => (w n : ℂ))
      b
      hNM
  have hprefix_N :
      (∑ i ∈ Finset.range (N + 1), b i) = 0 := by
    calc
      (∑ i ∈ Finset.range (N + 1), b i) =
          ∑ n ∈ Finset.Ioc N N, a n :=
        Complex.zeroExtended_tail_prefix_sum_eq_Ioc (a := a) N N
      _ = 0 := by
        exact Finset.sum_empty
  have hprefix_M :
      (∑ i ∈ Finset.range (M + 1), b i) =
        ∑ n ∈ Finset.Ioc N M, a n :=
    Complex.zeroExtended_tail_prefix_sum_eq_Ioc (a := a) N M
  have hprefix :
      ∀ k : ℕ,
        (∑ i ∈ Finset.range (k + 1), b i) =
          ∑ n ∈ Finset.Ioc N k, a n := by
    intro k
    exact Complex.zeroExtended_tail_prefix_sum_eq_Ioc (a := a) N k
  have hlhs :
      (∑ n ∈ Finset.Ioc N M, (w n : ℂ) • b n) =
        ∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        let hNn : N < n := (Finset.mem_Ioc.mp hn).1
        show (w n : ℂ) * a n = a n * (w n : ℂ) from
          mul_comm (w n : ℂ) (a n))
  have hrhs :
      (w M : ℂ) • (∑ i ∈ Finset.range (M + 1), b i) -
          (w (N + 1) : ℂ) • (∑ i ∈ Finset.range (N + 1), b i) -
            ∑ i ∈ Finset.Ioc N (M - 1),
              (((w (i + 1) : ℂ) - (w i : ℂ)) •
                (∑ x ∈ Finset.range (i + 1), b x)) =
        (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) +
          ∑ k ∈ Finset.Ioc N (M - 1),
            ((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ n ∈ Finset.Ioc N k, a n) := by
    calc
      (w M : ℂ) • (∑ i ∈ Finset.range (M + 1), b i) -
          (w (N + 1) : ℂ) • (∑ i ∈ Finset.range (N + 1), b i) -
            ∑ i ∈ Finset.Ioc N (M - 1),
              (((w (i + 1) : ℂ) - (w i : ℂ)) •
                (∑ x ∈ Finset.range (i + 1), b x)) =
          (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) -
            (w (N + 1) : ℂ) * 0 -
              ∑ i ∈ Finset.Ioc N (M - 1),
                (((w (i + 1) : ℂ) - (w i : ℂ)) •
                  (∑ x ∈ Finset.range (i + 1), b x)) := by
        congr 1 <;> exact hprefix_M
      _ = (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) -
            ∑ i ∈ Finset.Ioc N (M - 1),
              (((w (i + 1) : ℂ) - (w i : ℂ)) •
                  (∑ x ∈ Finset.range (i + 1), b x)) := by
        exact sub_zero _
      _ = (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) +
            ∑ k ∈ Finset.Ioc N (M - 1),
              ((w k - w (k + 1) : ℝ) : ℂ) *
                (∑ n ∈ Finset.Ioc N k, a n) := by
        congr 1
        exact Finset.sum_congr rfl
          (fun k hk =>
            let hpk :
                ∑ x ∈ Finset.range (k + 1), b x =
                  ∑ n ∈ Finset.Ioc N k, a n :=
              hprefix k
            show -(((w (k + 1) : ℂ) - (w k : ℂ)) *
                (∑ n ∈ Finset.Ioc N k, a n)) =
              ((w k - w (k + 1) : ℝ) : ℂ) * (∑ n ∈ Finset.Ioc N k, a n) from by
              exact Complex.neg_sub_mul_eq_ofReal_sub_mul_for_abelTail
                (w k) (w (k + 1))
                (∑ n ∈ Finset.Ioc N k, a n))
  exact Eq.trans hlhs.symm (Eq.trans hparts hrhs)

/-- The coefficient mass in the finite Abel identity is bounded by the initial
weight when the weights are positive and decreasing. -/
theorem Complex.finite_weighted_tail_abel_coefficient_mass_eq_initial
    {w : ℕ → ℝ}
    (N M : ℕ)
    (hNM : N < M) :
    w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) = w (N + 1) := by
  have hstart : N + 1 ≤ M := Nat.succ_le_of_lt hNM
  exact Nat.le_induction
    (by
      have htop : (N + 1) - 1 = N := Nat.succ_sub_one N
      calc
        w (N + 1) + ∑ k ∈ Finset.Ioc N ((N + 1) - 1), (w k - w (k + 1)) =
            w (N + 1) + ∑ k ∈ Finset.Ioc N N, (w k - w (k + 1)) := by
          exact congrArg
            (fun x : ℕ => w (N + 1) + ∑ k ∈ Finset.Ioc N x, (w k - w (k + 1)))
            htop
        _ = w (N + 1) := by
          have hsum : ∑ k ∈ Finset.Ioc N N, (w k - w (k + 1)) = 0 := by
            exact Finset.sum_empty
          calc
            w (N + 1) + ∑ k ∈ Finset.Ioc N N, (w k - w (k + 1)) =
                w (N + 1) + 0 := by
              exact congrArg (fun x : ℝ => w (N + 1) + x) hsum
            _ = w (N + 1) := add_zero (w (N + 1)))
    (fun m hm ih =>
      by
        have hNm : N < m := Nat.lt_of_succ_le hm
        have hNm_pred : N ≤ m - 1 := Nat.le_sub_one_of_lt hNm
        have hsub : (m + 1) - 1 = m := Nat.succ_sub_one m
        calc
          w (m + 1) + ∑ k ∈ Finset.Ioc N ((m + 1) - 1), (w k - w (k + 1)) =
              w (m + 1) + ∑ k ∈ Finset.Ioc N m, (w k - w (k + 1)) := by
            exact congrArg
              (fun x : ℕ => w (m + 1) + ∑ k ∈ Finset.Ioc N x, (w k - w (k + 1)))
              hsub
          _ = w (m + 1) +
              (∑ k ∈ Finset.Ioc N (m - 1), (w k - w (k + 1)) +
                (w m - w (m + 1))) := by
            have hsplit :
                ∑ k ∈ Finset.Ioc N m, (w k - w (k + 1)) =
                  ∑ k ∈ Finset.Ioc N (m - 1), (w k - w (k + 1)) +
                    (w m - w (m + 1)) :=
              sum_Ioc_succ_top hNm_pred
            exact congrArg (fun x : ℝ => w (m + 1) + x) hsplit
          _ = w m + ∑ k ∈ Finset.Ioc N (m - 1), (w k - w (k + 1)) :=
            Real.coefficient_mass_step_arithmetic_for_abelTail
              (w (m + 1))
              (w m)
              (∑ k ∈ Finset.Ioc N (m - 1), (w k - w (k + 1)))
          _ = w (N + 1) := ih)
    M hstart

theorem Complex.finite_weighted_tail_abel_coefficient_mass_le_one
    {w : ℕ → ℝ}
    (N M : ℕ)
    (hNM : N < M)
    (hw_nonneg : ∀ n : ℕ, N < n → 0 ≤ w n)
    (hw_antitone : ∀ {m n : ℕ}, N < m → m ≤ n → w n ≤ w m)
    (hw_initial : ∀ n : ℕ, N < n → w n ≤ 1) :
    w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) ≤ 1 := by
  calc
    w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) =
        w (N + 1) :=
      Complex.finite_weighted_tail_abel_coefficient_mass_eq_initial N M hNM
    _ ≤ 1 := hw_initial (N + 1) (Nat.lt_succ_self N)

theorem Complex.finite_weighted_tail_bound_of_uniform_finite_tail_bound
    {a : ℕ → ℂ}
    {B : ℝ}
    {w : ℕ → ℝ}
    (N : ℕ)
    (hN : 1 ≤ N)
    (hw_nonneg : ∀ n : ℕ, N < n → 0 ≤ w n)
    (hw_antitone : ∀ {m n : ℕ}, N < m → m ≤ n → w n ≤ w m)
    (hw_initial : ∀ n : ℕ, N < n → w n ≤ 1)
    (hfinite :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ B) :
    ∀ M : ℕ,
      N ≤ M →
        ‖∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ)‖ ≤ B := by
  intro M hNM_le
  exact
    match Classical.em (N < M) with
    | Or.inl hNM =>
      by
        have hB_nonneg : 0 ≤ B := by
          have hzero_bound := hfinite N (le_rfl : N ≤ N)
          exact hzero_bound
        have hid :
            (∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ)) =
              (w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) +
                ∑ k ∈ Finset.Ioc N (M - 1),
                  ((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                    (∑ n ∈ Finset.Ioc N k, a n) :=
          Complex.finite_weighted_tail_abel_identity N M hNM
        have hmass :
            w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) ≤ 1 :=
          Complex.finite_weighted_tail_abel_coefficient_mass_le_one
            N M hNM hw_nonneg hw_antitone hw_initial
        have hcoeff_M_nonneg : 0 ≤ w M :=
          hw_nonneg M hNM
        have hcoeff_nonneg :
            ∀ k ∈ Finset.Ioc N (M - 1), 0 ≤ w k - w (k + 1) := by
          intro k hk
          have hNk : N < k := (Finset.mem_Ioc.mp hk).1
          have hmono : w (k + 1) ≤ w k :=
            hw_antitone hNk (Nat.le_succ k)
          exact sub_nonneg.mpr hmono
        calc
          ‖∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ)‖ =
              ‖(w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n) +
                ∑ k ∈ Finset.Ioc N (M - 1),
                  ((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                    (∑ n ∈ Finset.Ioc N k, a n)‖ := by
            exact congrArg Norm.norm hid
          _ ≤ ‖(w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n)‖ +
                ‖∑ k ∈ Finset.Ioc N (M - 1),
                  ((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                    (∑ n ∈ Finset.Ioc N k, a n)‖ :=
            norm_add_le _ _
          _ ≤ w M * B +
                ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) * B := by
            apply add_le_add
            · calc
                ‖(w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n)‖ =
                    w M * ‖∑ n ∈ Finset.Ioc N M, a n‖ := by
                  have hnorm :
                      ‖(w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n)‖ =
                        ‖(w M : ℂ)‖ * ‖∑ n ∈ Finset.Ioc N M, a n‖ :=
                    norm_mul _ _
                  have hcoef : ‖(w M : ℂ)‖ = w M := by
                    have hcoef' : ‖(w M : ℂ)‖ = ‖w M‖ := Complex.norm_ofReal (w M)
                    exact Eq.trans hcoef' (abs_of_nonneg hcoeff_M_nonneg)
                  calc
                    ‖(w M : ℂ) * (∑ n ∈ Finset.Ioc N M, a n)‖ =
                        ‖(w M : ℂ)‖ * ‖∑ n ∈ Finset.Ioc N M, a n‖ := hnorm
                    _ = w M * ‖∑ n ∈ Finset.Ioc N M, a n‖ := by
                      congr
                      exact hcoef
                _ ≤ w M * B :=
                  mul_le_mul_of_nonneg_left (hfinite M hNM_le) hcoeff_M_nonneg
            · calc
                ‖∑ k ∈ Finset.Ioc N (M - 1),
                  ((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                    (∑ n ∈ Finset.Ioc N k, a n)‖
                    ≤ ∑ k ∈ Finset.Ioc N (M - 1),
                        ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                          (∑ n ∈ Finset.Ioc N k, a n)‖ :=
                  norm_sum_le _ _
                _ ≤ ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) * B := by
                  exact Finset.sum_le_sum
                    (fun k hk =>
                      let hNk : N < k := (Finset.mem_Ioc.mp hk).1
                      let hNk_le : N ≤ k := le_of_lt hNk
                      let hk_nonneg : 0 ≤ w k - w (k + 1) := hcoeff_nonneg k hk
                      calc
                        ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                            (∑ n ∈ Finset.Ioc N k, a n)‖ =
                            (w k - w (k + 1)) *
                              ‖∑ n ∈ Finset.Ioc N k, a n‖ := by
                          have hnorm :
                              ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                                  (∑ n ∈ Finset.Ioc N k, a n)‖ =
                                ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ)‖ *
                                  ‖∑ n ∈ Finset.Ioc N k, a n‖ :=
                            norm_mul _ _
                          have hcoef : ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ)‖ =
                              (w k - w (k + 1)) := by
                            have hcoef' : ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ)‖ =
                                ‖w k - w (k + 1)‖ := Complex.norm_ofReal _
                            exact Eq.trans hcoef' (abs_of_nonneg hk_nonneg)
                          calc
                            ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ) *
                                (∑ n ∈ Finset.Ioc N k, a n)‖ =
                                ‖((w k - w (k + 1 : ℕ) : ℝ) : ℂ)‖ *
                                  ‖∑ n ∈ Finset.Ioc N k, a n‖ := hnorm
                            _ = (w k - w (k + 1)) *
                                  ‖∑ n ∈ Finset.Ioc N k, a n‖ := by
                              congr
                              exact hcoef
                        _ ≤ (w k - w (k + 1)) * B :=
                          mul_le_mul_of_nonneg_left (hfinite k hNk_le) hk_nonneg)
          _ = (w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1))) * B := by
            have hsum_mul :
                ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) * B =
                  (∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1))) * B :=
              Finset.sum_mul _ _
            calc
              w M * B + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)) * B =
                  w M * B +
                    (∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1))) * B := by
                exact congrArg (fun x : ℝ => w M * B + x) hsum_mul
              _ = (w M + ∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1))) * B := by
                exact (add_mul (w M)
                  (∑ k ∈ Finset.Ioc N (M - 1), (w k - w (k + 1)))
                  B).symm
          _ ≤ 1 * B :=
            mul_le_mul_of_nonneg_right hmass hB_nonneg
          _ = B := one_mul B
    | Or.inr hNM =>
      by
        have hMN : M ≤ N := le_of_not_gt hNM
        have hempty : Finset.Ioc N M = ∅ := Finset.Ioc_eq_empty_of_le hMN
        have hzero_bound := hfinite N le_rfl
        exact hzero_bound

/-- Passage from uniformly bounded finite weighted tails to the corresponding
`tsum`. -/
theorem Complex.tsum_weighted_tail_bound_of_finite_weighted_tail_bound
    {a : ℕ → ℂ}
    {B : ℝ}
    {w : ℕ → ℝ}
    (N : ℕ)
    (hsummable :
      Summable
        (fun n : ℕ =>
          if N < n then a n * (w n : ℂ) else 0))
    (hfinite_weighted :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n * (w n : ℂ)‖ ≤ B) :
    ‖∑' n : ℕ,
      if N < n then a n * (w n : ℂ) else 0‖ ≤ B := by
  let f : ℕ → ℂ := fun n : ℕ =>
    if N < n then a n * (w n : ℂ) else 0
  have hlim :
      Tendsto
        (fun K : ℕ => ∑ n ∈ Finset.range (K + (N + 1)), f n)
        atTop
        (𝓝 (∑' n : ℕ, f n)) := by
    exact hsummable.hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat (N + 1))
  have hbounded :
      ∀ K : ℕ,
        ‖∑ n ∈ Finset.range (K + (N + 1)), f n‖ ≤ B := by
    intro K
    have hsum_eq :
        (∑ n ∈ Finset.range (K + (N + 1)), f n) =
          ∑ n ∈ Finset.Ioc N (N + K), a n * (w n : ℂ) := by
      have hfilter :
          (Finset.range (K + (N + 1))).filter (fun n : ℕ => N < n) =
            Finset.Ioc N (N + K) := by
        ext n
        constructor
        · intro hn
          have hn_range : n < K + (N + 1) :=
            Finset.mem_range.mp (Finset.mem_filter.mp hn).1
          have hNn : N < n :=
            (Finset.mem_filter.mp hn).2
          have htop : K + (N + 1) = (N + K) + 1 := by
            calc
              K + (N + 1) = (K + N) + 1 := by
                exact Nat.add_assoc K N 1
              _ = (N + K) + 1 := by
                exact congrArg (fun x : ℕ => x + 1) (Nat.add_comm K N)
          have hn_lt_top : n < (N + K) + 1 :=
            Eq.subst (motive := fun q : ℕ => n < q) htop hn_range
          have hn_le : n ≤ N + K :=
            Nat.le_of_lt_succ hn_lt_top
          exact Finset.mem_Ioc.mpr ⟨hNn, hn_le⟩
        · intro hn
          have hNn : N < n := (Finset.mem_Ioc.mp hn).1
          have hn_le : n ≤ N + K := (Finset.mem_Ioc.mp hn).2
          have htop : K + (N + 1) = (N + K) + 1 := by
            calc
              K + (N + 1) = (K + N) + 1 := by
                exact Nat.add_assoc K N 1
              _ = (N + K) + 1 := by
                exact congrArg (fun x : ℕ => x + 1) (Nat.add_comm K N)
          have hn_range : n < K + (N + 1) :=
            Eq.subst
              (motive := fun q : ℕ => n < q)
              htop.symm
              (Nat.lt_succ_of_le hn_le)
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hn_range, hNn⟩
      calc
        (∑ n ∈ Finset.range (K + (N + 1)), f n) =
            ∑ n ∈ (Finset.range (K + (N + 1))).filter
              (fun n : ℕ => N < n), a n * (w n : ℂ) := by
          exact Finset.sum_filter
      _ = ∑ n ∈ Finset.Ioc N (N + K), a n * (w n : ℂ) := by
          exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, a n * (w n : ℂ)) hfilter
    have hNK : N ≤ N + K := Nat.le.intro rfl
    exact hsum_eq.trans_le (hfinite_weighted (N + K) hNK)
  have hnorm_lim :
      Tendsto
        (fun K : ℕ => ‖∑ n ∈ Finset.range (K + (N + 1)), f n‖)
        atTop
        (𝓝 ‖∑' n : ℕ, f n‖) :=
    hlim.norm
  have hconst :
      Tendsto (fun _ : ℕ => B) atTop (𝓝 B) :=
    tendsto_const_nhds
  have hle :
      ‖∑' n : ℕ, f n‖ ≤ B :=
    le_of_tendsto_of_tendsto' hnorm_lim hconst hbounded
  exact hle

/-- Abstract Abel damping lemma with explicit weight hypotheses. -/
theorem Complex.abelDampedTail_bound_of_uniform_finite_tail_bound'
    {a : ℕ → ℂ}
    {B : ℝ}
    {w : ℝ → ℕ → ℝ}
    (N : ℕ)
    (hN : 1 ≤ N)
    (hw_nonneg :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ n : ℕ, N < n → 0 ≤ w σ n)
    (hw_antitone :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ {m n : ℕ}, N < m → m ≤ n → w σ n ≤ w σ m)
    (hw_initial :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ n : ℕ, N < n → w σ n ≤ 1)
    (hsummable :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        Summable
          (fun n : ℕ =>
            if N < n then a n * (w σ n : ℂ) else 0))
    (hfinite :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ B) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' n : ℕ,
        if N < n then
          a n * (w σ n : ℂ)
        else
          0‖ ≤ B := by
  filter_upwards [hw_nonneg, hw_antitone, hw_initial, hsummable] with
    σ hσ_nonneg hσ_antitone hσ_initial hσ_summable
  have hfinite_weighted :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n * (w σ n : ℂ)‖ ≤ B :=
    Complex.finite_weighted_tail_bound_of_uniform_finite_tail_bound
      N hN hσ_nonneg hσ_antitone hσ_initial hfinite
  exact
    Complex.tsum_weighted_tail_bound_of_finite_weighted_tail_bound
      N hσ_summable hfinite_weighted

/-- Explicit unordered summability carrier for Abel weights.

Bounded ordinary Dirichlet tails give ordered Nat partial-sum convergence, not
unordered `Summable` in the sense needed by `tsum`; the latter is kept as an
honest hypothesis and supplied by absolute convergence in the boundary-line
application. -/
theorem Complex.abelDampedTail_summable_of_uniform_finite_tail_bound
    {a : ℕ → ℂ}
    (N : ℕ)
    (hfinite :
      ∃ B : ℝ,
        ∀ M : ℕ,
          N ≤ M →
            ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ B) :
    (∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      Summable
        (fun n : ℕ =>
          if N < n then
            a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0)) →
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      Summable
        (fun n : ℕ =>
          if N < n then
            a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
          else
            0) := by
  intro hsummable
  exact hsummable

/-- Abel damping by the concrete weights `n ^ (-(σ - 1))` preserves a uniform
finite-tail bound. -/
theorem Complex.abelDampedTail_bound_of_uniform_finite_tail_bound
    {a : ℕ → ℂ}
    {B : ℝ}
    (N : ℕ)
    (hN : 1 ≤ N)
    (hsummable :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        Summable
          (fun n : ℕ =>
            if N < n then
              a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
            else
              0))
    (hfinite :
      ∀ M : ℕ,
        N ≤ M →
          ‖∑ n ∈ Finset.Ioc N M, a n‖ ≤ B) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' n : ℕ,
        if N < n then
          a n * ((n : ℝ) ^ (-(σ - 1)) : ℂ)
        else
          0‖ ≤ B := by
  have hsummable :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        Summable
          (fun n : ℕ =>
            if N < n then
              a n * (((fun σ n => (n : ℝ) ^ (-(σ - 1))) σ n) : ℂ)
            else
              0) := by
    exact
      Complex.abelDampedTail_summable_of_uniform_finite_tail_bound
        (a := a) N ⟨B, hfinite⟩ hsummable
  have hw_nonneg :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ n : ℕ, N < n → 0 ≤ (n : ℝ) ^ (-(σ - 1)) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ n hn
    exact Real.rpow_nonneg (Nat.cast_nonneg n) (-(σ - 1))
  have hw_antitone :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ {m n : ℕ}, N < m → m ≤ n →
          (n : ℝ) ^ (-(σ - 1)) ≤ (m : ℝ) ^ (-(σ - 1)) := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ m n hm hmn
    have hm_pos : 0 < (m : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.lt_of_le_of_lt (Nat.zero_le N) hm)
    have hmn_real : (m : ℝ) ≤ (n : ℝ) := by
      exact Nat.cast_le.mpr hmn
    have hexp_nonpos : -(σ - 1) ≤ 0 := by
      exact neg_nonpos.mpr (sub_nonneg.mpr (le_of_lt hσ))
    exact Real.rpow_le_rpow_of_nonpos hm_pos hmn_real hexp_nonpos
  have hw_initial :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ∀ n : ℕ, N < n → (n : ℝ) ^ (-(σ - 1)) ≤ 1 := by
    filter_upwards [eventually_mem_nhdsWithin] with σ hσ n hn
    have hn_one : 1 ≤ (n : ℝ) := by
      have hn_nat : 1 ≤ n := le_trans hN (Nat.succ_le_of_lt hn)
      exact Nat.cast_le.mpr hn_nat
    have hexp_nonpos : -(σ - 1) ≤ 0 := by
      exact neg_nonpos.mpr (sub_nonneg.mpr (le_of_lt hσ))
    exact Real.rpow_le_one_of_one_le_of_nonpos hn_one hexp_nonpos
  exact
    Complex.abelDampedTail_bound_of_uniform_finite_tail_bound'
      (a := a)
      (B := B)
      (w := fun σ n => (n : ℝ) ^ (-(σ - 1)))
      N hN hw_nonneg hw_antitone hw_initial hsummable hfinite

end

end LFunctions
end Boundary
