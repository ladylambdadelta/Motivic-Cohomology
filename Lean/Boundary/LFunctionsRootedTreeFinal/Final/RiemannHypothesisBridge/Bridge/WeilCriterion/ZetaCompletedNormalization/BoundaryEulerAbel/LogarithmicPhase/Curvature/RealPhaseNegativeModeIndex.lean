import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseInverseSquareRootSum
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessCenterFrequencyTransport

/-!
# Positive indices for negative Fourier modes

All logarithmic stationary modes are negative integers.  Their absolute values
are positive natural indices, and this transport is injective on every
negative-mode family.  The exact cast identity `natAbs m = -(m : ℝ)` connects
the stationary center formula to inverse-square-root summation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseNegativeModeIndex (m : ℤ) : ℕ :=
  Int.natAbs m

theorem Complex.logarithmicPhaseNegativeModeIndex_pos
    {m : ℤ} (hm : m < 0) :
    0 < Complex.logarithmicPhaseNegativeModeIndex m := by
  unfold Complex.logarithmicPhaseNegativeModeIndex
  exact Int.natAbs_pos.mpr (ne_of_lt hm)

theorem Complex.logarithmicPhaseNegativeModeIndex_one_le
    {m : ℤ} (hm : m < 0) :
    1 ≤ Complex.logarithmicPhaseNegativeModeIndex m :=
  Nat.succ_le_of_lt
    (Complex.logarithmicPhaseNegativeModeIndex_pos hm)

theorem Real.negative_int_cast_eq_neg_natAbs_cast
    {m : ℤ} (hm : m ≤ 0) :
    (m : ℝ) = -((Int.natAbs m : ℕ) : ℝ) := by
  have hint : (m.natAbs : ℤ) = -m := Int.natCast_natAbs_of_nonpos hm
  have hcast := congrArg (fun value : ℤ => (value : ℝ)) hint
  have hleft : (((m.natAbs : ℕ) : ℤ) : ℝ) = ((m.natAbs : ℕ) : ℝ) :=
    Int.cast_ofNat m.natAbs
  have hright : ((-m : ℤ) : ℝ) = -(m : ℝ) := Int.cast_neg m
  have habs : ((m.natAbs : ℕ) : ℝ) = -(m : ℝ) :=
    Eq.subst (motive := fun left : ℝ => left = -(m : ℝ))
      hleft.symm
      (Eq.subst (motive := fun right : ℝ =>
        (((m.natAbs : ℕ) : ℤ) : ℝ) = right) hright.symm hcast)
  exact neg_eq_iff_eq_neg.mpr habs.symm

theorem Real.neg_int_cast_eq_natAbs_cast
    {m : ℤ} (hm : m ≤ 0) :
    -(m : ℝ) = ((Int.natAbs m : ℕ) : ℝ) := by
  exact Eq.trans
    (congrArg Neg.neg (Real.negative_int_cast_eq_neg_natAbs_cast hm))
    (neg_neg _)

theorem Complex.logarithmicPhaseNegativeModeIndex_cast_eq
    {m : ℤ} (hm : m < 0) :
    ((Complex.logarithmicPhaseNegativeModeIndex m : ℕ) : ℝ) =
      -(m : ℝ) := by
  unfold Complex.logarithmicPhaseNegativeModeIndex
  exact (Real.neg_int_cast_eq_natAbs_cast (le_of_lt hm)).symm

theorem Complex.logarithmicPhaseNegativeModeIndex_injectiveOn
    (M : Finset ℤ)
    (hM : ∀ m ∈ M, m < 0) :
    Set.InjOn Complex.logarithmicPhaseNegativeModeIndex M := by
  intro m hm n hn heq
  have hmNonpos := le_of_lt (hM m hm)
  have hnNonpos := le_of_lt (hM n hn)
  have hmCast := Real.negative_int_cast_eq_neg_natAbs_cast hmNonpos
  have hnCast := Real.negative_int_cast_eq_neg_natAbs_cast hnNonpos
  have hnatCast := congrArg (fun value : ℕ => (value : ℝ)) heq
  have hreal : (m : ℝ) = (n : ℝ) :=
    Eq.trans hmCast
      (Eq.trans (congrArg Neg.neg hnatCast) hnCast.symm)
  exact Int.cast_injective hreal

def Complex.logarithmicPhaseNegativeModeIndexSet
    (M : Finset ℤ) : Finset ℕ :=
  M.image Complex.logarithmicPhaseNegativeModeIndex

theorem Complex.mem_logarithmicPhaseNegativeModeIndexSet_iff
    (M : Finset ℤ) (k : ℕ) :
    k ∈ Complex.logarithmicPhaseNegativeModeIndexSet M ↔
      ∃ m ∈ M, Complex.logarithmicPhaseNegativeModeIndex m = k := by
  unfold Complex.logarithmicPhaseNegativeModeIndexSet
  exact Finset.mem_image

theorem Complex.logarithmicPhaseNegativeModeIndexSet_card_eq
    (M : Finset ℤ)
    (hM : ∀ m ∈ M, m < 0) :
    (Complex.logarithmicPhaseNegativeModeIndexSet M).card = M.card := by
  unfold Complex.logarithmicPhaseNegativeModeIndexSet
  exact Finset.card_image_iff.mpr (fun m hm n hn heq =>
    Complex.logarithmicPhaseNegativeModeIndex_injectiveOn M hM hm hn heq)

theorem Complex.logarithmicPhaseNegativeModeIndexSet_subset_Icc
    (M : Finset ℤ) (N : ℕ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMupper : ∀ m ∈ M, Complex.logarithmicPhaseNegativeModeIndex m ≤ N) :
    Complex.logarithmicPhaseNegativeModeIndexSet M ⊆ Finset.Icc 1 N := by
  intro k hk
  have hmem :=
    (Complex.mem_logarithmicPhaseNegativeModeIndexSet_iff M k).mp hk
  obtain ⟨m, hm, hmk⟩ := hmem
  have hlower := Complex.logarithmicPhaseNegativeModeIndex_one_le (hMneg m hm)
  have hupper := hMupper m hm
  exact Finset.mem_Icc.mpr
    (And.intro
      (Eq.subst (motive := fun value : ℕ => 1 ≤ value) hmk hlower)
      (Eq.subst (motive := fun value : ℕ => value ≤ N) hmk hupper))

theorem Complex.sum_negativeModes_eq_sum_indexImage
    (M : Finset ℤ)
    (hM : ∀ m ∈ M, m < 0)
    (f : ℕ → ℝ) :
    (∑ m ∈ M, f (Complex.logarithmicPhaseNegativeModeIndex m)) =
      ∑ k ∈ Complex.logarithmicPhaseNegativeModeIndexSet M, f k := by
  unfold Complex.logarithmicPhaseNegativeModeIndexSet
  exact Eq.trans
    (Finset.sum_image
      (fun m hm n hn heq =>
        Complex.logarithmicPhaseNegativeModeIndex_injectiveOn M hM hm hn heq)
      f)
    rfl

theorem Complex.sum_negativeMode_invSqrt_le_full_Icc
    (M : Finset ℤ) (N : ℕ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMupper : ∀ m ∈ M, Complex.logarithmicPhaseNegativeModeIndex m ≤ N) :
    (∑ m ∈ M,
        (Real.sqrt
          (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹) ≤
      ∑ k ∈ Finset.Icc 1 N, (Real.sqrt (k : ℝ))⁻¹ := by
  have hrewrite := Complex.sum_negativeModes_eq_sum_indexImage
    M hMneg (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹)
  have hsubset := Complex.logarithmicPhaseNegativeModeIndexSet_subset_Icc
    M N hMneg hMupper
  have hnonneg : ∀ k ∈ Finset.Icc 1 N,
      0 ≤ (Real.sqrt (k : ℝ))⁻¹ :=
    fun k hk => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun k hk hnot => hnonneg k hk)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hrewrite.symm hmono

theorem Complex.sum_negativeMode_invSqrt_le_two_sqrt
    (M : Finset ℤ) (N : ℕ)
    (hMneg : ∀ m ∈ M, m < 0)
    (hMupper : ∀ m ∈ M, Complex.logarithmicPhaseNegativeModeIndex m ≤ N) :
    (∑ m ∈ M,
        (Real.sqrt
          (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))⁻¹) ≤
      2 * Real.sqrt (N : ℝ) :=
  le_trans
    (Complex.sum_negativeMode_invSqrt_le_full_Icc M N hMneg hMupper)
    (Real.sum_Icc_inv_sqrt_le_two_sqrt N)

theorem Complex.logarithmicPhase_stationaryCenter_eq_norm_div_modeIndex
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m =
      ‖t‖ /
        (2 * Real.pi *
          (Complex.logarithmicPhaseNegativeModeIndex m : ℝ)) := by
  have hangular := Complex.logarithmicPhaseAngular_eq_norm_div_center
    t ht hm
  have hindex := Complex.logarithmicPhaseNegativeModeIndex_cast_eq hm
  have hdenom :
      2 * Real.pi * (-(m : ℝ)) =
        2 * Real.pi *
          (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) :=
    congrArg (fun value : ℝ => 2 * Real.pi * value) hindex.symm
  have hcenterPos := Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hangularPos : 0 < 2 * Real.pi * (-(m : ℝ)) := by
    have hmCastNeg : (m : ℝ) < 0 := Int.cast_neg.mpr hm
    exact mul_pos Complex.two_mul_pi_pos (neg_pos.mpr hmCastNeg)
  have hsolve := (eq_div_iff hangularPos.ne').mpr hangular.symm
  exact Eq.trans hsolve
    (congrArg (fun denominator : ℝ => ‖t‖ / denominator) hdenom)

end

end LFunctions
end Boundary
