import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualAmplitude

/-!
# Finite Abel summation for the dual logarithmic phase

This owner proves the shifted finite summation-by-parts identity used for the
dual stationary packets.  If

`S(j) = z(K) + ... + z(K+j)`,

then

`sum_{j=0}^N w(K+j) z(K+j)`

is the terminal weight times `S(N)`, plus the sum of forward weight drops
times the earlier partial sums.  For a nonnegative antitone amplitude and a
uniform bound `B` for all dual phase partial sums, the weighted sum is at most
`2*w(K)*B`.  Every cancellation and norm transition is named explicitly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.shiftedInclusivePartialSum
    (z : ℕ → ℂ) (K j : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), z (K + i)

def Complex.shiftedWeightedRangeSum
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, (w (K + j) : ℂ) * z (K + j)

def Complex.shiftedAbelVariationSum
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N,
    ((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
      Complex.shiftedInclusivePartialSum z K j

theorem Complex.shiftedInclusivePartialSum_zero
    (z : ℕ → ℂ) (K : ℕ) :
    Complex.shiftedInclusivePartialSum z K 0 = z K := by
  unfold Complex.shiftedInclusivePartialSum
  have hrange : Finset.range (0 + 1) = {0} := by
    exact Finset.range_one
  exact Eq.trans
    (congrArg (fun s : Finset ℕ => ∑ i ∈ s, z (K + i)) hrange)
    (Eq.trans (Finset.sum_singleton 0 (fun i : ℕ => z (K + i)))
      (congrArg z (Nat.add_zero K)))

theorem Complex.shiftedInclusivePartialSum_succ
    (z : ℕ → ℂ) (K j : ℕ) :
    Complex.shiftedInclusivePartialSum z K (j + 1) =
      Complex.shiftedInclusivePartialSum z K j + z (K + (j + 1)) := by
  unfold Complex.shiftedInclusivePartialSum
  have hsuccessor : j + 1 + 1 = (j + 1) + 1 := rfl
  exact Finset.sum_range_succ (fun i : ℕ => z (K + i)) (j + 1)

theorem Complex.shiftedInclusivePartialSum_increment
    (z : ℕ → ℂ) (K j : ℕ) :
    z (K + (j + 1)) =
      Complex.shiftedInclusivePartialSum z K (j + 1) -
        Complex.shiftedInclusivePartialSum z K j := by
  have hsum := Complex.shiftedInclusivePartialSum_succ z K j
  exact (eq_sub_iff_add_eq).mpr
    (Eq.trans (add_comm _ _) hsum.symm)

theorem Complex.realCast_sub_mul
    (a b : ℝ) (z : ℂ) :
    (((a - b : ℝ) : ℂ) * z) =
      (a : ℂ) * z - (b : ℂ) * z := by
  exact Eq.trans
    (congrArg (fun c : ℂ => c * z) (Complex.ofReal_sub a b))
    (sub_mul (a : ℂ) (b : ℂ) z)

theorem Complex.abel_two_term_cancellation
    (a b : ℝ) (S T : ℂ) :
    (a : ℂ) * S +
        (((a - b : ℝ) : ℂ) * T + (b : ℂ) * (S - T)) =
      (a : ℂ) * S + (a : ℂ) * T - (b : ℂ) * T +
        ((b : ℂ) * S - (b : ℂ) * T) := by
  have hvariation := Complex.realCast_sub_mul a b T
  have hincrement := mul_sub (b : ℂ) S T
  exact congrArg
    (fun x : ℂ => (a : ℂ) * S + x)
    (Eq.trans
      (congrArg₂ (fun x y : ℂ => x + y) hvariation hincrement)
      (add_sub_assoc _ _ _))

theorem Complex.abel_terminal_shift
    (a b : ℝ) (S T : ℂ) :
    (a : ℂ) * T + (((a - b : ℝ) : ℂ) * S) +
        (b : ℂ) * (T - S) =
      (a : ℂ) * T := by
  have hvariation := Complex.realCast_sub_mul a b S
  have hincrement := mul_sub (b : ℂ) T S
  calc
    (a : ℂ) * T + (((a - b : ℝ) : ℂ) * S) +
        (b : ℂ) * (T - S) =
      (a : ℂ) * T + ((a : ℂ) * S - (b : ℂ) * S) +
        ((b : ℂ) * T - (b : ℂ) * S) := by
          exact congrArg₂ (fun x y : ℂ => (a : ℂ) * T + x + y)
            hvariation hincrement
    _ = (a : ℂ) * T +
        ((a : ℂ) * S + (b : ℂ) * T) -
          ((b : ℂ) * S + (b : ℂ) * S) := by
            exact Eq.trans
              (add_assoc ((a : ℂ) * T)
                ((a : ℂ) * S - (b : ℂ) * S)
                ((b : ℂ) * T - (b : ℂ) * S)).symm
              (congrArg (fun x : ℂ => (a : ℂ) * T + x)
                (sub_add_sub_comm
                  ((a : ℂ) * S) ((b : ℂ) * S)
                  ((b : ℂ) * T) ((b : ℂ) * S)))
    _ = (a : ℂ) * T := by
      have hcancel :
          ((a : ℂ) * S - (b : ℂ) * S) +
              ((b : ℂ) * T - (b : ℂ) * S) +
                (b : ℂ) * (T - S) = 0 := by
        exact sub_eq_zero.mp rfl
      exact Eq.trans
        (congrArg (fun z : ℂ => (a : ℂ) * T + z) hcancel)
        (add_zero _)

/-- Exact finite Abel identity on `N+1` shifted terms. -/
theorem Complex.shiftedWeightedRangeSum_succ_eq_abel
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) :
    Complex.shiftedWeightedRangeSum w z K (N + 1) =
      (w (K + N) : ℂ) *
          Complex.shiftedInclusivePartialSum z K N +
        Complex.shiftedAbelVariationSum w z K N := by
  induction N with
  | zero =>
      unfold Complex.shiftedWeightedRangeSum
      unfold Complex.shiftedAbelVariationSum
      have hweighted := Finset.sum_range_succ
        (fun j : ℕ => (w (K + j) : ℂ) * z (K + j)) 0
      have hvariation :
          (∑ j ∈ Finset.range 0,
            (((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
              Complex.shiftedInclusivePartialSum z K j)) = 0 :=
        Finset.sum_range_zero _
      exact Eq.trans hweighted
        (Eq.trans
          (congrArg₂ (fun x y : ℂ => x + y)
            (congrArg₂ (fun a b : ℂ => a * b)
              (congrArg (fun n : ℕ => (w n : ℂ)) (Nat.add_zero K))
              (Complex.shiftedInclusivePartialSum_zero z K).symm)
            hvariation.symm)
          (add_zero _).symm)
  | succ N ih =>
      have hweightedSucc := Finset.sum_range_succ
        (fun j : ℕ => (w (K + j) : ℂ) * z (K + j)) (N + 1)
      have hvariationSucc := Finset.sum_range_succ
        (fun j : ℕ =>
          (((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
            Complex.shiftedInclusivePartialSum z K j)) N
      have hincrement := Complex.shiftedInclusivePartialSum_increment z K N
      have hindex : K + (N + 1) = K + N + 1 := by
        exact Eq.trans (Nat.add_assoc K N 1) rfl
      unfold Complex.shiftedWeightedRangeSum at ih
      unfold Complex.shiftedAbelVariationSum at ih
      unfold Complex.shiftedWeightedRangeSum
      unfold Complex.shiftedAbelVariationSum
      exact Eq.trans hweightedSucc
        (Eq.trans
          (congrArg
            (fun q : ℂ =>
              q + (w (K + (N + 1)) : ℂ) * z (K + (N + 1))) ih)
          (Eq.trans
            (congrArg
              (fun q : ℂ =>
                (w (K + N) : ℂ) *
                    Complex.shiftedInclusivePartialSum z K N + q +
                  (w (K + (N + 1)) : ℂ) * z (K + (N + 1)))
              hvariationSucc.symm)
            (by
              have hstep := Complex.abel_terminal_shift
                (w (K + N)) (w (K + N + 1))
                (Complex.shiftedInclusivePartialSum z K N)
                (Complex.shiftedInclusivePartialSum z K (N + 1))
              exact Eq.trans
                (congrArg
                  (fun q : ℂ =>
                    (∑ j ∈ Finset.range N,
                      (((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
                        Complex.shiftedInclusivePartialSum z K j)) + q)
                  (Eq.trans
                    (congrArg₂ (fun x y : ℂ =>
                        (w (K + N) : ℂ) *
                            Complex.shiftedInclusivePartialSum z K N + x + y)
                      rfl
                      (Eq.trans
                        (congrArg
                          (fun q : ℂ =>
                            (w (K + (N + 1)) : ℂ) * q)
                          hincrement)
                        (congrArg
                          (fun q : ℂ => (w q : ℂ) *
                            (Complex.shiftedInclusivePartialSum z K (N + 1) -
                              Complex.shiftedInclusivePartialSum z K N))
                          hindex)))
                    hstep))
                (add_comm _ _))))

theorem Complex.norm_shiftedInclusivePartialSum_le
    (z : ℕ → ℂ) (K j : ℕ) {B : ℝ}
    (hpartial :
      ∀ q ≤ j,
        ‖Complex.shiftedInclusivePartialSum z K q‖ ≤ B) :
    ‖Complex.shiftedInclusivePartialSum z K j‖ ≤ B := by
  exact hpartial j (Nat.le_refl j)

theorem Complex.norm_shiftedAbelVariationSummand_le
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K j : ℕ) {B : ℝ}
    (hdrop : 0 ≤ w (K + j) - w (K + j + 1))
    (hpartial : ‖Complex.shiftedInclusivePartialSum z K j‖ ≤ B) :
    ‖(((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
        Complex.shiftedInclusivePartialSum z K j‖ ≤
      (w (K + j) - w (K + j + 1)) * B := by
  have hdropNorm :
      ‖((w (K + j) - w (K + j + 1) : ℝ) : ℂ)‖ =
        w (K + j) - w (K + j + 1) := by
    exact Complex.norm_real_of_nonneg hdrop
  have hmul := mul_le_mul_of_nonneg_left hpartial hdrop
  exact Eq.subst (motive := fun q : ℝ => q ≤ _)
    (Eq.trans
      (norm_mul
        ((w (K + j) - w (K + j + 1) : ℝ) : ℂ)
        (Complex.shiftedInclusivePartialSum z K j))
      (congrArg
        (fun q : ℝ =>
          q * ‖Complex.shiftedInclusivePartialSum z K j‖)
        hdropNorm)).symm hmul

theorem Complex.norm_shiftedAbelVariationSum_le
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) {B : ℝ}
    (hdrop : ∀ j < N, 0 ≤ w (K + j) - w (K + j + 1))
    (hpartial : ∀ j < N,
      ‖Complex.shiftedInclusivePartialSum z K j‖ ≤ B) :
    ‖Complex.shiftedAbelVariationSum w z K N‖ ≤
      (∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1))) * B := by
  unfold Complex.shiftedAbelVariationSum
  have hnormSum := norm_sum_le
    (Finset.range N)
    (fun j : ℕ =>
      (((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
        Complex.shiftedInclusivePartialSum z K j))
  have hpoint :
      (∑ j ∈ Finset.range N,
        ‖(((w (K + j) - w (K + j + 1) : ℝ) : ℂ) *
          Complex.shiftedInclusivePartialSum z K j‖) ≤
      ∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1)) * B := by
    exact Finset.sum_le_sum (fun j hj =>
      Complex.norm_shiftedAbelVariationSummand_le w z K j
        (hdrop j (Finset.mem_range.mp hj))
        (hpartial j (Finset.mem_range.mp hj)))
  have hfactor :
      (∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1)) * B) =
      (∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1))) * B := by
    exact Finset.sum_mul
      (Finset.range N)
      (fun j : ℕ => w (K + j) - w (K + j + 1)) B
  exact le_trans hnormSum
    (le_trans hpoint (le_of_eq hfactor))

theorem Complex.norm_shiftedWeightedRangeSum_succ_le_abel
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) {B : ℝ}
    (hweight : 0 ≤ w (K + N))
    (hdrop : ∀ j < N, 0 ≤ w (K + j) - w (K + j + 1))
    (hpartial : ∀ j ≤ N,
      ‖Complex.shiftedInclusivePartialSum z K j‖ ≤ B) :
    ‖Complex.shiftedWeightedRangeSum w z K (N + 1)‖ ≤
      w (K + N) * B +
        (∑ j ∈ Finset.range N,
          (w (K + j) - w (K + j + 1))) * B := by
  have hidentity :=
    Complex.shiftedWeightedRangeSum_succ_eq_abel w z K N
  have htriangle := norm_add_le
    ((w (K + N) : ℂ) * Complex.shiftedInclusivePartialSum z K N)
    (Complex.shiftedAbelVariationSum w z K N)
  have hterminalNorm :
      ‖(w (K + N) : ℂ) *
          Complex.shiftedInclusivePartialSum z K N‖ ≤
        w (K + N) * B := by
    have hcast : ‖(w (K + N) : ℂ)‖ = w (K + N) :=
      Complex.norm_real_of_nonneg hweight
    have hscaled := mul_le_mul_of_nonneg_left
      (hpartial N (Nat.le_refl N)) hweight
    exact Eq.subst (motive := fun q : ℝ => q ≤ _)
      (Eq.trans
        (norm_mul (w (K + N) : ℂ)
          (Complex.shiftedInclusivePartialSum z K N))
        (congrArg
          (fun q : ℝ => q *
            ‖Complex.shiftedInclusivePartialSum z K N‖) hcast)).symm
      hscaled
  have hvariation :=
    Complex.norm_shiftedAbelVariationSum_le w z K N B hdrop
      (fun j hj => hpartial j (Nat.le_of_lt_succ hj))
  have hsum := add_le_add hterminalNorm hvariation
  exact Eq.subst (motive := fun q : ℂ => ‖q‖ ≤ _)
    hidentity.symm (le_trans htriangle hsum)

theorem Complex.logarithmicPhaseDualWeightedRangeSum_le_two_initial_mul
    (t : ℝ) (K N : ℕ) (hK : 0 < K) {B : ℝ}
    (hpartial : ∀ j ≤ N,
      ‖Complex.shiftedInclusivePartialSum
          (Complex.logarithmicPhaseDualOscillationNat t) K j‖ ≤ B)
    (hB : 0 ≤ B) :
    ‖Complex.shiftedWeightedRangeSum
        (Complex.logarithmicPhaseDualStationaryAmplitudeNat t)
        (Complex.logarithmicPhaseDualOscillationNat t) K (N + 1)‖ ≤
      2 *
        (Complex.logarithmicPhaseDualStationaryAmplitudeNat t K * B) := by
  let w := Complex.logarithmicPhaseDualStationaryAmplitudeNat t
  let z := Complex.logarithmicPhaseDualOscillationNat t
  have hweight : 0 ≤ w (K + N) :=
    Complex.logarithmicPhaseDualStationaryAmplitude_nonneg t ((K + N : ℕ) : ℝ)
  have hdrop : ∀ j < N, 0 ≤ w (K + j) - w (K + j + 1) := by
    intro j hj
    have hKj : 0 < K + j := lt_of_lt_of_le hK (Nat.le_add_right K j)
    exact
      Complex.logarithmicPhaseDualStationaryAmplitudeNat_difference_nonneg
        t hKj
  have habel :=
    Complex.norm_shiftedWeightedRangeSum_succ_le_abel
      w z K N hweight hdrop hpartial
  have hvariationEq := Finset.sum_range_forwardDifference
    (fun j : ℕ => w (K + j)) N
  have hterminalLeInitial : w (K + N) ≤ w K :=
    Complex.logarithmicPhaseDualStationaryAmplitudeNat_antitone
      t hK (Nat.le_add_right K N)
  have hvariationLeInitial :
      (∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1))) ≤ w K := by
    have hfinal :=
      Complex.logarithmicPhaseDualStationaryAmplitude_nonneg
        t ((K + N : ℕ) : ℝ)
    have hdropInitial := sub_le_self (w K) hfinal
    exact Eq.subst (motive := fun q : ℝ => q ≤ w K)
      hvariationEq.symm hdropInitial
  have hterminalScaled := mul_le_mul_of_nonneg_right
    hterminalLeInitial hB
  have hvariationScaled := mul_le_mul_of_nonneg_right
    hvariationLeInitial hB
  have hcombined := add_le_add hterminalScaled hvariationScaled
  have hnormalize : w K * B + w K * B = 2 * (w K * B) :=
    (two_mul (w K * B)).symm
  exact le_trans habel
    (le_trans hcombined (le_of_eq hnormalize))

end

end LFunctions
end Boundary
