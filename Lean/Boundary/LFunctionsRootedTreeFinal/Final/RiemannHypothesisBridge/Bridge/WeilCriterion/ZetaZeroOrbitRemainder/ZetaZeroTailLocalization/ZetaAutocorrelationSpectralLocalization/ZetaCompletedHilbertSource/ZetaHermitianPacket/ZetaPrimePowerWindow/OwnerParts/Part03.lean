import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.OwnerParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section
open scoped BigOperators

namespace ZetaPrimePowerIndex

/-- The finite window part of a prime-power family. -/
noncomputable def windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    ZetaPrimePowerIndex → ℝ :=
  fun ι =>
    if ι ∈ window N then
      u ι
    else
      0

/-- The outside-window tail part of a prime-power family. -/
noncomputable def spectralTail
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    ZetaPrimePowerIndex → ℝ :=
  fun ι =>
    if ι ∈ window N then
      0
    else
      u ι

/-- The finite window part and outside-window tail reconstruct the original family
coordinatewise. -/
theorem windowPart_add_spectralTail_apply
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) (ι : ZetaPrimePowerIndex) :
    windowPart u N ι + spectralTail u N ι = u ι := by
  by_cases hι : ι ∈ window N
  · have hleft : windowPart u N ι = u ι := by
      unfold windowPart
      exact if_pos hι
    have hright : spectralTail u N ι = 0 := by
      unfold spectralTail
      exact if_pos hι
    calc
      windowPart u N ι + spectralTail u N ι
          = u ι + spectralTail u N ι := by
              exact congrArg (fun x : ℝ => x + spectralTail u N ι) hleft
      _ = u ι + 0 := by
              exact congrArg (fun x : ℝ => u ι + x) hright
      _ = u ι := by
              exact add_zero (u ι)
  · have hleft : windowPart u N ι = 0 := by
      unfold windowPart
      exact if_neg hι
    have hright : spectralTail u N ι = u ι := by
      unfold spectralTail
      exact if_neg hι
    calc
      windowPart u N ι + spectralTail u N ι
          = 0 + spectralTail u N ι := by
              exact congrArg (fun x : ℝ => x + spectralTail u N ι) hleft
      _ = 0 + u ι := by
              exact congrArg (fun x : ℝ => 0 + x) hright
      _ = u ι := by
              exact zero_add (u ι)

/-- The finite window part and outside-window tail reconstruct the original family. -/
theorem windowPart_add_spectralTail
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    (fun ι : ZetaPrimePowerIndex => windowPart u N ι + spectralTail u N ι) = u := by
  funext ι
  exact windowPart_add_spectralTail_apply u N ι

/-- The outside-window tail is the original family minus its finite window part,
coordinatewise. -/
theorem spectralTail_eq_original_sub_windowPart_apply
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) (ι : ZetaPrimePowerIndex) :
    spectralTail u N ι = u ι - windowPart u N ι := by
  by_cases hι : ι ∈ window N
  · have htail : spectralTail u N ι = 0 := by
      unfold spectralTail
      exact if_pos hι
    have hwindow : windowPart u N ι = u ι := by
      unfold windowPart
      exact if_pos hι
    calc
      spectralTail u N ι
          = 0 := htail
      _ = u ι - u ι := by
              exact (sub_self (u ι)).symm
      _ = u ι - windowPart u N ι := by
              exact congrArg (fun x : ℝ => u ι - x) hwindow.symm
  · have htail : spectralTail u N ι = u ι := by
      unfold spectralTail
      exact if_neg hι
    have hwindow : windowPart u N ι = 0 := by
      unfold windowPart
      exact if_neg hι
    calc
      spectralTail u N ι
          = u ι := htail
      _ = u ι - 0 := by
              exact (sub_zero (u ι)).symm
      _ = u ι - windowPart u N ι := by
              exact congrArg (fun x : ℝ => u ι - x) hwindow.symm

/-- The outside-window tail is the original family minus its finite window part. -/
theorem spectralTail_eq_original_sub_windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    spectralTail u N =
      fun ι : ZetaPrimePowerIndex => u ι - windowPart u N ι := by
  funext ι
  exact spectralTail_eq_original_sub_windowPart_apply u N ι

/-- The finite indicator vanishes off its finite support. -/
theorem finsetIndicator_eq_zero_of_not_mem
    {α : Type*} [DecidableEq α]
    (s : Finset α) (u : α → ℝ) {a : α}
    (ha : a ∉ s) :
    (if a ∈ s then
      u a
    else
      0) = 0 := by
  exact if_neg ha

/-- A function that vanishes off a finset has infinite sum equal to its finite sum over
that finset. -/
theorem hasSum_of_eq_zero_off_finset
    {α : Type*} [DecidableEq α]
    (s : Finset α) (v : α → ℝ)
    (hv : ∀ a : α, a ∉ s → v a = 0) :
    HasSum v (∑ a in s, v a) := by
  exact hasSum_sum_of_ne_finset_zero hv

/-- A real-valued function cut out by a finite indicator has infinite sum equal to the
corresponding finite sum. -/
theorem hasSum_finsetIndicator
    {α : Type*} [DecidableEq α]
    (s : Finset α) (u : α → ℝ) :
    HasSum
      (fun a : α =>
        if a ∈ s then
          u a
        else
          0)
      (∑ a in s, u a) := by
  let v : α → ℝ :=
    fun a : α =>
      if a ∈ s then
        u a
      else
        0
  have hv : ∀ a : α, a ∉ s → v a = 0 := by
    intro a ha
    unfold v
    exact finsetIndicator_eq_zero_of_not_mem s u ha
  have hsum_v : HasSum v (∑ a in s, v a) :=
    hasSum_of_eq_zero_off_finset s v hv
  have hsum_eq :
      (∑ a in s, v a) = ∑ a in s, u a := by
    exact Finset.sum_congr rfl
      (fun a ha =>
        (fun hmem : a ∈ s =>
          by
            unfold v
            exact if_pos hmem) ha)
  exact Eq.subst
    (motive := fun x : ℝ => HasSum v x)
    hsum_eq
    hsum_v

/-- The finite window part has sum equal to its finite window sum. -/
theorem windowPart_hasSum_windowSum
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    HasSum (windowPart u N) (∑ ι in window N, u ι) := by
  exact hasSum_finsetIndicator (window N) u

/-- A finite window part is summable. -/
theorem summable_windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    Summable (windowPart u N) := by
  exact (windowPart_hasSum_windowSum u N).summable

/-- The finite window part has `tsum` equal to its finite window sum. -/
theorem windowPart_tsum_eq_windowSum
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) =
      ∑ ι in window N, u ι := by
  exact (windowPart_hasSum_windowSum u N).tsum_eq

/-- The outside-window tail of a summable family is summable. -/
theorem summable_spectralTail_of_summable
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    Summable (spectralTail u N) := by
  have hwindow : Summable (windowPart u N) :=
    summable_windowPart u N
  have hsub :
      Summable (fun ι : ZetaPrimePowerIndex => u ι - windowPart u N ι) :=
    hsum.sub hwindow
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ => Summable v)
    (spectralTail_eq_original_sub_windowPart u N).symm
    hsub

/-- The `tsum` of a summable family splits into its finite window part and its
outside-window tail. -/
theorem tsum_eq_windowPart_tsum_add_spectralTail_tsum
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex, u ι) =
      (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
        (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) := by
  have hwindow : Summable (windowPart u N) :=
    summable_windowPart u N
  have htail : Summable (spectralTail u N) :=
    summable_spectralTail_of_summable u hsum N
  have hsplit :
      (∑' ι : ZetaPrimePowerIndex,
        (windowPart u N ι + spectralTail u N ι)) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) :=
    tsum_add hwindow htail
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ =>
      (∑' ι : ZetaPrimePowerIndex, v ι) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι))
    (windowPart_add_spectralTail u N)
    hsplit

/-- The complement tail of a summable prime-window family is the total `tsum` minus the
finite window sum. -/
theorem spectralTail_eq_tsum_sub_windowSum
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex,
      if ι ∈ window N then
        0
      else
        u ι) =
      (∑' ι : ZetaPrimePowerIndex, u ι) -
        ∑ ι in window N, u ι := by
  have hsplit :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) :=
    tsum_eq_windowPart_tsum_add_spectralTail_tsum u hsum N
  have hwindow :
      (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) =
        ∑ ι in window N, u ι :=
    windowPart_tsum_eq_windowSum u N
  have htail_fun :
      (fun ι : ZetaPrimePowerIndex =>
        if ι ∈ window N then
          0
        else
          u ι) =
        spectralTail u N := by
    funext ι
    rfl
  have htotal :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        (∑ ι in window N, u ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) := by
    exact hsplit.trans
      (congrArg
        (fun x : ℝ =>
          x + (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι))
        hwindow)
  have htail :
      (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) -
          ∑ ι in window N, u ι := by
    calc
      (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)
          = ((∑ ι in window N, u ι) +
              (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)) -
              ∑ ι in window N, u ι := by
              exact (add_sub_cancel_left
                (∑ ι in window N, u ι)
                (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)).symm
      _ = (∑' ι : ZetaPrimePowerIndex, u ι) -
              ∑ ι in window N, u ι := by
              exact congrArg
                (fun x : ℝ => x - ∑ ι in window N, u ι)
                htotal.symm
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ =>
      (∑' ι : ZetaPrimePowerIndex, v ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) -
          ∑ ι in window N, u ι)
    htail_fun.symm
    htail

/-- The outside-window tail sum of a summable prime-power family vanishes along the
prime-power windows. -/
theorem spectralTail_tsum_tendsto_zero_of_summable
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → u ι = 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)
      Filter.atTop
      (nhds 0) := by
  have hwindow :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in window N, u ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    tendsto_sum_window_tsum_of_summable u hsum hzero
  have hconstant :
      Filter.Tendsto
        (fun _N : ℕ => ∑' ι : ZetaPrimePowerIndex, u ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    tendsto_const_nhds
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in window N, u ι)
        Filter.atTop
        (nhds
          ((∑' ι : ZetaPrimePowerIndex, u ι) -
            (∑' ι : ZetaPrimePowerIndex, u ι))) :=
    hconstant.sub hwindow
  have htarget :
      (∑' ι : ZetaPrimePowerIndex, u ι) -
          (∑' ι : ZetaPrimePowerIndex, u ι) =
        0 :=
    sub_self (∑' ι : ZetaPrimePowerIndex, u ι)
  have htail_fun :
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) =
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in window N, u ι) := by
    funext N
    exact spectralTail_eq_tsum_sub_windowSum u hsum N
  exact Eq.subst
    (motive := fun v : ℕ → ℝ =>
      Filter.Tendsto v Filter.atTop (nhds 0))
    htail_fun.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (∑' ι : ZetaPrimePowerIndex, u ι) -
              ∑ ι in window N, u ι)
          Filter.atTop
          (nhds x))
      htarget
      hsub)

/-- A summable real tail is bounded by a nonnegative summable majorant tail when each
coordinate norm is bounded by the majorant. -/
theorem norm_spectralTail_tsum_le_spectralTail_tsum_of_norm_le
    (u v : ZetaPrimePowerIndex → ℝ)
    (hv : Summable v)
    (hbound : ∀ ι : ZetaPrimePowerIndex, ‖u ι‖ ≤ v ι)
    (N : ℕ) :
    ‖(∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)‖ ≤
      ∑' ι : ZetaPrimePowerIndex, spectralTail v N ι := by
  have htail_v : Summable (spectralTail v N) :=
    summable_spectralTail_of_summable v hv N
  have hpoint :
      ∀ ι : ZetaPrimePowerIndex,
        ‖spectralTail u N ι‖ ≤ spectralTail v N ι := by
    intro ι
    by_cases hι : ι ∈ window N
    · have hu_zero : spectralTail u N ι = 0 := by
        unfold spectralTail
        exact if_pos hι
      have hv_zero : spectralTail v N ι = 0 := by
        unfold spectralTail
        exact if_pos hι
      calc
        ‖spectralTail u N ι‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm hu_zero
        _ = 0 := by
          exact norm_zero
        _ ≤ spectralTail v N ι := by
          exact le_of_eq hv_zero.symm
    · have hu_value : spectralTail u N ι = u ι := by
        unfold spectralTail
        exact if_neg hι
      have hv_value : spectralTail v N ι = v ι := by
        unfold spectralTail
        exact if_neg hι
      calc
        ‖spectralTail u N ι‖ = ‖u ι‖ := by
          exact congrArg norm hu_value
        _ ≤ v ι := hbound ι
        _ = spectralTail v N ι := by
          exact hv_value.symm
  have htail_u_norm :
      Summable (fun ι : ZetaPrimePowerIndex => ‖spectralTail u N ι‖) := by
    exact Summable.of_norm_bounded (spectralTail v N) htail_v
      (fun ι =>
        calc
          ‖‖spectralTail u N ι‖‖ = ‖spectralTail u N ι‖ := by
            exact norm_norm (spectralTail u N ι)
          _ ≤ spectralTail v N ι := hpoint ι)
  have hnorm_tsum :
      ‖(∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)‖ ≤
        ∑' ι : ZetaPrimePowerIndex, ‖spectralTail u N ι‖ :=
    norm_tsum_le_tsum_norm htail_u_norm
  have hmajorant_tsum :
      (∑' ι : ZetaPrimePowerIndex, ‖spectralTail u N ι‖) ≤
        ∑' ι : ZetaPrimePowerIndex, spectralTail v N ι :=
    tsum_le_tsum hpoint htail_u_norm htail_v
  exact hnorm_tsum.trans hmajorant_tsum

/-- Membership in a prime-power window exposes genuine prime-power data. -/
theorem isGenuine_of_mem_window
    (N : ℕ) (ι : ZetaPrimePowerIndex) (hι : ι ∈ window N) :
    IsGenuine ι := by
  have hmem := (mem_window_iff N ι).mp hι
  exact ⟨hmem.2.2.1, hmem.2.2.2⟩

/-- Prime-power windows are monotone in the natural cutoff. -/
theorem window_mono {N M : ℕ} (hNM : N ≤ M) :
    window N ⊆ window M := by
  intro ι hι
  have hmem := (mem_window_iff N ι).mp hι
  have hp : ι.p < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.1) hNM)
  have hn : ι.n < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.2.1) hNM)
  exact (mem_window_iff M ι).mpr ⟨hp, hn, hmem.2.2.1, hmem.2.2.2⟩

/-- A genuine prime-power index eventually belongs to every sufficiently large rectangular
prime-power window. -/
theorem eventually_mem_window_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    ∀ᶠ N : ℕ in Filter.atTop, ι ∈ window N := by
  exact Filter.eventually_atTop.2
    ⟨max ι.p ι.n,
      fun N hN =>
        have hp_le : ι.p ≤ N := le_trans (Nat.le_max_left ι.p ι.n) hN
        have hn_le : ι.n ≤ N := le_trans (Nat.le_max_right ι.p ι.n) hN
        have hp_lt : ι.p < N + 1 := Nat.lt_succ_of_le hp_le
        have hn_lt : ι.n < N + 1 := Nat.lt_succ_of_le hn_le
        (mem_window_iff N ι).mpr ⟨hp_lt, hn_lt, hι.1, hι.2⟩⟩

end ZetaPrimePowerIndex

end
end LFunctions
end Boundary
