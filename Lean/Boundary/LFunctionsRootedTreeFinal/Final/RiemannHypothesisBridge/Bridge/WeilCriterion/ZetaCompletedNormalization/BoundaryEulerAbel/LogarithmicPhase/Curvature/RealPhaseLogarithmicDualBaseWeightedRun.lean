import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBaseRunBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualAbel

/-!
# Abel-weighted bounds on base dual principal runs

The uniform prefix estimate on a principal run is inserted into the exact
finite Abel identity.  A run of length `L` is normalized as `N+1` terms with
`N=L-1`; all index conversions are stated separately.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualRunLength
    (p : ℕ × ℕ) : ℕ := p.2 - p.1

def Complex.logarithmicPhaseDualRunAbelIndex
    (p : ℕ × ℕ) : ℕ :=
  Complex.logarithmicPhaseDualRunLength p - 1

theorem Complex.logarithmicPhaseDualRunLength_pos
    {p : ℕ × ℕ} (hp : p.1 < p.2) :
    0 < Complex.logarithmicPhaseDualRunLength p := by
  unfold Complex.logarithmicPhaseDualRunLength
  exact Nat.sub_pos_of_lt hp

theorem Complex.logarithmicPhaseDualRunAbelIndex_succ_eq_length
    {p : ℕ × ℕ} (hp : p.1 < p.2) :
    Complex.logarithmicPhaseDualRunAbelIndex p + 1 =
      Complex.logarithmicPhaseDualRunLength p := by
  unfold Complex.logarithmicPhaseDualRunAbelIndex
  have hpos := Complex.logarithmicPhaseDualRunLength_pos hp
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)

theorem Complex.logarithmicPhaseDualRun_start_add_length
    {p : ℕ × ℕ} (hp : p.1 ≤ p.2) :
    p.1 + Complex.logarithmicPhaseDualRunLength p = p.2 := by
  unfold Complex.logarithmicPhaseDualRunLength
  exact Nat.add_sub_of_le hp

theorem Complex.shiftedWeightedRangeSum_eq_Ico
    (w : ℕ → ℝ) (z : ℕ → ℂ) (K N : ℕ) :
    Complex.shiftedWeightedRangeSum w z K N =
      ∑ n ∈ Finset.Ico K (K + N), (w n : ℂ) * z n := by
  unfold Complex.shiftedWeightedRangeSum
  have hmap := Finset.Ico_eq_map_range K N
  exact Eq.trans
    (Finset.sum_bij
      (fun j hj => K + j)
      (fun j hj => by
        exact Eq.subst (motive := fun S : Finset ℕ => K + j ∈ S)
          hmap.symm (Finset.mem_map.mpr
            (Exists.intro j (And.intro hj rfl))))
      (fun j hj => rfl)
      (fun j₁ hj₁ j₂ hj₂ heq => Nat.add_left_cancel heq)
      (fun n hn =>
        have hnMap : n ∈ (Finset.range N).map
            ⟨fun j : ℕ => K + j,
              fun x y hxy => Nat.add_left_cancel hxy⟩ :=
          Eq.subst (motive := fun S : Finset ℕ => n ∈ S) hmap hn
        Finset.mem_map.mp hnMap))
    rfl

theorem Complex.shiftedInclusivePartialSum_eq_Ico
    (z : ℕ → ℂ) (K j : ℕ) :
    Complex.shiftedInclusivePartialSum z K j =
      ∑ n ∈ Finset.Ico K (K + j + 1), z n := by
  unfold Complex.shiftedInclusivePartialSum
  have hmap := Finset.Ico_eq_map_range K (j + 1)
  have hendpoint : K + (j + 1) = K + j + 1 := Nat.add_assoc K j 1
  exact Eq.trans
    (Finset.sum_bij
      (fun i hi => K + i)
      (fun i hi => by
        exact Eq.subst (motive := fun S : Finset ℕ => K + i ∈ S)
          hmap.symm (Finset.mem_map.mpr
            (Exists.intro i (And.intro hi rfl))))
      (fun i hi => rfl)
      (fun i₁ hi₁ i₂ hi₂ heq => Nat.add_left_cancel heq)
      (fun n hn =>
        have hnIco : n ∈ Finset.Ico K (K + (j + 1)) :=
          Eq.subst (motive := fun endpoint : ℕ => n ∈ Finset.Ico K endpoint)
            hendpoint.symm hn
        have hnMap : n ∈ (Finset.range (j + 1)).map
            ⟨fun i : ℕ => K + i,
              fun x y hxy => Nat.add_left_cancel hxy⟩ :=
          Eq.subst (motive := fun S : Finset ℕ => n ∈ S) hmap hnIco
        Finset.mem_map.mp hnMap))
    rfl

theorem Complex.logarithmicPhaseDualBasePrincipalRun_shiftedPrefix_norm_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} (heta : 0 < eta)
    {K M : ℕ} (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    (hpNonempty : p.1 < p.2) :
    ∀ j ≤ Complex.logarithmicPhaseDualRunAbelIndex p,
      ‖Complex.shiftedInclusivePartialSum
          (Complex.logarithmicPhaseDualOscillationNat t) p.1 j‖ ≤
        4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹ := by
  intro j hj
  have hsuccLe : j + 1 ≤ Complex.logarithmicPhaseDualRunLength p := by
    exact Eq.subst (motive := fun z : ℕ => j + 1 ≤ z)
      (Complex.logarithmicPhaseDualRunAbelIndex_succ_eq_length hpNonempty)
      (Nat.add_le_add_right hj 1)
  have hend : p.1 + j + 1 ≤ p.2 := by
    have hscaled := Nat.add_le_add_left hsuccLe p.1
    exact Eq.subst (motive := fun z : ℕ => p.1 + j + 1 ≤ z)
      (Complex.logarithmicPhaseDualRun_start_add_length
        (le_of_lt hpNonempty)) hscaled
  have hprefix :=
    Complex.logarithmicPhaseDualBasePrincipalRun_prefix_norm_le
      t ht heta hK hp (p.1 + j + 1)
      (lt_of_lt_of_le (Nat.lt_succ_self (p.1 + j))
        (Nat.le_add_right (p.1 + j) 1)) hend
  exact Eq.subst (motive := fun z : ℂ => ‖z‖ ≤ _)
    (Complex.shiftedInclusivePartialSum_eq_Ico
      (Complex.logarithmicPhaseDualOscillationNat t) p.1 j).symm
    hprefix

theorem Complex.logarithmicPhaseDualBasePrincipalRun_weighted_norm_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} (heta : 0 < eta)
    {K M : ℕ} (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    (hpNonempty : p.1 < p.2) :
    ‖∑ n ∈ Finset.Ico p.1 p.2,
        Complex.logarithmicPhaseDualBProcessWeightedTerm t n‖ ≤
      2 * (Complex.logarithmicPhaseDualBProcessAmplitudeNat t p.1 *
        (4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹)) := by
  let B := 4 * (eta⁻¹ + 1) + 4 * Real.pi * eta⁻¹
  have hB : 0 ≤ B := by
    have hetaInv : 0 ≤ eta⁻¹ := le_of_lt (inv_pos.mpr heta)
    exact add_nonneg
      (mul_nonneg (le_of_lt zero_lt_four) (add_nonneg hetaInv zero_le_one))
      (mul_nonneg
        (mul_nonneg (le_of_lt zero_lt_four) (le_of_lt Real.pi_pos)) hetaInv)
  have hprefix :=
    Complex.logarithmicPhaseDualBasePrincipalRun_shiftedPrefix_norm_le
      t ht heta hK hp hpNonempty
  have habel :=
    Complex.logarithmicPhaseDualBProcessWeightedRangeSum_le_two_initial_mul
      t p.1 (Complex.logarithmicPhaseDualRunAbelIndex p)
      (lt_of_lt_of_le hK
        (Complex.logarithmicPhaseDualBasePrincipalRun_bounded
          t eta K M hp).1)
      hprefix hB
  have hlength :=
    Complex.logarithmicPhaseDualRunAbelIndex_succ_eq_length hpNonempty
  have hendpoint := Complex.logarithmicPhaseDualRun_start_add_length
    (le_of_lt hpNonempty)
  have hsum := Complex.shiftedWeightedRangeSum_eq_Ico
    (Complex.logarithmicPhaseDualBProcessAmplitudeNat t)
    (Complex.logarithmicPhaseDualOscillationNat t)
    p.1 (Complex.logarithmicPhaseDualRunAbelIndex p + 1)
  exact Eq.subst (motive := fun z : ℂ => ‖z‖ ≤ _)
    (Eq.trans
      (Finset.sum_congr rfl
        (fun n hn => Eq.refl
          (Complex.logarithmicPhaseDualBProcessWeightedTerm t n)))
      (Eq.trans
        (congrArg
          (fun endpoint : ℕ =>
            ∑ n ∈ Finset.Ico p.1 endpoint,
              (Complex.logarithmicPhaseDualBProcessAmplitudeNat t n : ℂ) *
                Complex.logarithmicPhaseDualOscillationNat t n)
          (Eq.trans
            (congrArg (fun z : ℕ => p.1 + z) hlength)
            hendpoint))
        hsum.symm)).symm habel

end

end LFunctions
end Boundary
