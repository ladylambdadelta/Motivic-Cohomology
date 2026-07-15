import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicNonDyadicEndpointPacket

/-!
# Frequency-scale interval split

Wide logarithmic blocks are split at `floor ‖t‖`.  The prefix contains all
stationary frequencies at the natural frequency scale.  The strict right tail
starts at the successor cutoff and is assigned to first-derivative analysis.
This owner contains only exact floor arithmetic and finite-set decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseFrequencyCutoff (t : ℝ) : ℕ :=
  ⌊‖t‖⌋₊

def Real.logarithmicPhaseFrequencyTailStart (t : ℝ) : ℕ :=
  Real.logarithmicPhaseFrequencyCutoff t + 1

theorem Real.logarithmicPhaseFrequencyCutoff_cast_le
    (t : ℝ) :
    ((Real.logarithmicPhaseFrequencyCutoff t : ℕ) : ℝ) ≤ ‖t‖ := by
  unfold Real.logarithmicPhaseFrequencyCutoff
  exact Nat.floor_le (norm_nonneg t)

theorem Real.logarithmicPhaseFrequencyCutoff_one_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    1 ≤ Real.logarithmicPhaseFrequencyCutoff t := by
  unfold Real.logarithmicPhaseFrequencyCutoff
  exact (Nat.one_le_floor_iff ‖t‖).mpr ht

theorem Real.logarithmicPhaseFrequencyCutoff_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    0 < Real.logarithmicPhaseFrequencyCutoff t :=
  lt_of_lt_of_le Nat.zero_lt_one
    (Real.logarithmicPhaseFrequencyCutoff_one_le t ht)

theorem Real.logarithmicPhaseFrequencyCutoff_lt_norm_add_one
    (t : ℝ) :
    ((Real.logarithmicPhaseFrequencyCutoff t : ℕ) : ℝ) < ‖t‖ + 1 := by
  have hfloor := Real.logarithmicPhaseFrequencyCutoff_cast_le t
  exact lt_of_le_of_lt hfloor (lt_add_of_pos_right ‖t‖ zero_lt_one)

theorem Real.norm_lt_frequencyTailStart_cast
    (t : ℝ) :
    ‖t‖ < ((Real.logarithmicPhaseFrequencyTailStart t : ℕ) : ℝ) := by
  unfold Real.logarithmicPhaseFrequencyTailStart
  unfold Real.logarithmicPhaseFrequencyCutoff
  have hfloor := Nat.lt_floor_add_one ‖t‖
  have hcast : (((⌊‖t‖⌋₊ + 1 : ℕ) : ℝ)) =
      ((⌊‖t‖⌋₊ : ℕ) : ℝ) + 1 := by
    exact Eq.trans (Nat.cast_add ⌊‖t‖⌋₊ 1)
      (congrArg (fun value : ℝ => ((⌊‖t‖⌋₊ : ℕ) : ℝ) + value)
        Nat.cast_one)
  exact Eq.subst (motive := fun value : ℝ => ‖t‖ < value)
    hcast.symm hfloor

theorem Real.logarithmicPhaseFrequencyTailStart_pos
    (t : ℝ) :
    0 < Real.logarithmicPhaseFrequencyTailStart t := by
  unfold Real.logarithmicPhaseFrequencyTailStart
  exact Nat.succ_pos _

theorem Real.logarithmicPhaseFrequencyCutoff_le_tailStart
    (t : ℝ) :
    Real.logarithmicPhaseFrequencyCutoff t ≤
      Real.logarithmicPhaseFrequencyTailStart t := by
  unfold Real.logarithmicPhaseFrequencyTailStart
  exact Nat.le_succ _

theorem Real.logarithmicPhaseFrequencyCutoff_succ_eq_tailStart
    (t : ℝ) :
    Real.logarithmicPhaseFrequencyCutoff t + 1 =
      Real.logarithmicPhaseFrequencyTailStart t :=
  rfl

theorem Finset.Ico_frequencyCutoff_disjoint_Icc_tailStart
    (a b C : ℕ) :
    Disjoint (Finset.Ico a (C + 1)) (Finset.Icc (C + 1) b) := by
  exact Finset.disjoint_left.mpr (fun n hprefix htail =>
    have hp := Finset.mem_Ico.mp hprefix
    have ht := Finset.mem_Icc.mp htail
    (not_lt_of_ge ht.1) hp.2)

theorem Finset.Ico_union_Icc_successor_eq_Icc
    (a b C : ℕ)
    (haC : a ≤ C)
    (hCb : C ≤ b) :
    Finset.Ico a (C + 1) ∪ Finset.Icc (C + 1) b =
      Finset.Icc a b := by
  exact Finset.ext (fun n =>
    Iff.intro
      (fun hn =>
        have hu := Finset.mem_union.mp hn
        match hu with
        | Or.inl hp =>
            have hdata := Finset.mem_Ico.mp hp
            have hnC : n ≤ C := Nat.lt_succ_iff.mp hdata.2
            Finset.mem_Icc.mpr
              (And.intro hdata.1 (Nat.le_trans hnC hCb))
        | Or.inr ht =>
            have hdata := Finset.mem_Icc.mp ht
            Finset.mem_Icc.mpr
              (And.intro (Nat.le_trans haC (Nat.le_trans
                (Nat.le_succ C) hdata.1)) hdata.2))
      (fun hn =>
        have hdata := Finset.mem_Icc.mp hn
        match lt_or_ge n (C + 1) with
        | Or.inl hnC =>
            Finset.mem_union_left _
              (Finset.mem_Ico.mpr (And.intro hdata.1 hnC))
        | Or.inr hCn =>
            Finset.mem_union_right _
              (Finset.mem_Icc.mpr (And.intro hCn hdata.2))))

theorem Finset.sum_Icc_eq_prefix_add_frequencyTail
    {M : Type*} [AddCommMonoid M]
    (f : ℕ → M)
    (a b C : ℕ)
    (haC : a ≤ C)
    (hCb : C ≤ b) :
    (∑ n ∈ Finset.Icc a b, f n) =
      (∑ n ∈ Finset.Ico a (C + 1), f n) +
        ∑ n ∈ Finset.Icc (C + 1) b, f n := by
  have hunion := Finset.Ico_union_Icc_successor_eq_Icc a b C haC hCb
  have hdisjoint := Finset.Ico_frequencyCutoff_disjoint_Icc_tailStart a b C
  have hsum := Finset.sum_union hdisjoint f
  exact Eq.trans
    (congrArg (fun modes : Finset ℕ => ∑ n ∈ modes, f n) hunion.symm)
    hsum

theorem Finset.Ico_eq_Icc_of_successor
    (a C : ℕ) (haC : a ≤ C) :
    Finset.Ico a (C + 1) = Finset.Icc a C := by
  exact Finset.ext (fun n =>
    Iff.intro
      (fun hn =>
        have hdata := Finset.mem_Ico.mp hn
        Finset.mem_Icc.mpr
          (And.intro hdata.1 (Nat.lt_succ_iff.mp hdata.2)))
      (fun hn =>
        have hdata := Finset.mem_Icc.mp hn
        Finset.mem_Ico.mpr
          (And.intro hdata.1 (Nat.lt_succ_of_le hdata.2))))

theorem Finset.sum_Icc_eq_frequencyPrefix_add_tail
    {M : Type*} [AddCommMonoid M]
    (f : ℕ → M)
    (a b C : ℕ)
    (haC : a ≤ C)
    (hCb : C ≤ b) :
    (∑ n ∈ Finset.Icc a b, f n) =
      (∑ n ∈ Finset.Icc a C, f n) +
        ∑ n ∈ Finset.Icc (C + 1) b, f n := by
  have hsplit := Finset.sum_Icc_eq_prefix_add_frequencyTail
    f a b C haC hCb
  have hprefix := Finset.Ico_eq_Icc_of_successor a C haC
  exact Eq.trans hsplit
    (congrArg
      (fun value : M => value + ∑ n ∈ Finset.Icc (C + 1) b, f n)
      (congrArg (fun modes : Finset ℕ => ∑ n ∈ modes, f n) hprefix))

theorem Complex.logarithmicPhaseRealPhase_block_eq_frequencyPrefix_add_tail
    (t : ℝ) (a b : ℕ)
    (haCut : a ≤ Real.logarithmicPhaseFrequencyCutoff t)
    (hCutb : Real.logarithmicPhaseFrequencyCutoff t ≤ b) :
    (∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))) =
      (∑ n ∈ Finset.Icc a (Real.logarithmicPhaseFrequencyCutoff t),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))) +
      ∑ n ∈ Finset.Icc (Real.logarithmicPhaseFrequencyTailStart t) b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ)) := by
  exact Finset.sum_Icc_eq_frequencyPrefix_add_tail
    (fun n : ℕ =>
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ)))
    a b (Real.logarithmicPhaseFrequencyCutoff t) haCut hCutb

theorem Complex.logarithmicPhaseRealPhase_block_norm_le_frequencyPrefix_add_tail_norms
    (t : ℝ) (a b : ℕ)
    (haCut : a ≤ Real.logarithmicPhaseFrequencyCutoff t)
    (hCutb : Real.logarithmicPhaseFrequencyCutoff t ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      ‖∑ n ∈ Finset.Icc a (Real.logarithmicPhaseFrequencyCutoff t),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ +
      ‖∑ n ∈ Finset.Icc (Real.logarithmicPhaseFrequencyTailStart t) b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ))‖ := by
  have hsplit :=
    Complex.logarithmicPhaseRealPhase_block_eq_frequencyPrefix_add_tail
      t a b haCut hCutb
  exact Eq.subst
    (motive := fun value : ℂ => ‖value‖ ≤ _)
    hsplit.symm (norm_add_le _ _)

theorem Real.frequencyCutoff_endpointRatio_le_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    ((Real.logarithmicPhaseFrequencyCutoff t : ℕ) : ℝ) / ‖t‖ ≤ 1 := by
  have hnormPos := lt_of_lt_of_le zero_lt_one ht
  exact (div_le_one hnormPos).mpr
    (Real.logarithmicPhaseFrequencyCutoff_cast_le t)

theorem Real.frequencyCutoff_succ_div_norm_le_two
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    ((Real.logarithmicPhaseFrequencyCutoff t + 1 : ℕ) : ℝ) / ‖t‖ ≤ 2 := by
  have hnormPos := lt_of_lt_of_le zero_lt_one ht
  have hfloor := Real.logarithmicPhaseFrequencyCutoff_cast_le t
  have hsuccCast :
      (((Real.logarithmicPhaseFrequencyCutoff t + 1 : ℕ) : ℝ)) =
        ((Real.logarithmicPhaseFrequencyCutoff t : ℕ) : ℝ) + 1 := by
    exact Eq.trans
      (Nat.cast_add (Real.logarithmicPhaseFrequencyCutoff t) 1)
      (congrArg
        (fun value : ℝ =>
          ((Real.logarithmicPhaseFrequencyCutoff t : ℕ) : ℝ) + value)
        Nat.cast_one)
  have honeLeNorm : (1 : ℝ) ≤ ‖t‖ := ht
  have hnum :
      (((Real.logarithmicPhaseFrequencyCutoff t + 1 : ℕ) : ℝ)) ≤
        2 * ‖t‖ := by
    exact Eq.subst (motive := fun value : ℝ => value ≤ 2 * ‖t‖)
      hsuccCast.symm
      (le_trans (add_le_add hfloor honeLeNorm)
        (le_of_eq (two_mul ‖t‖).symm))
  have hdiv := div_le_div_of_nonneg_right hnum hnormPos.le
  have hnormalize : (2 * ‖t‖) / ‖t‖ = 2 :=
    mul_div_cancel_right₀ 2 (ne_of_gt hnormPos)
  exact le_trans hdiv (le_of_eq hnormalize)

end

end LFunctions
end Boundary
