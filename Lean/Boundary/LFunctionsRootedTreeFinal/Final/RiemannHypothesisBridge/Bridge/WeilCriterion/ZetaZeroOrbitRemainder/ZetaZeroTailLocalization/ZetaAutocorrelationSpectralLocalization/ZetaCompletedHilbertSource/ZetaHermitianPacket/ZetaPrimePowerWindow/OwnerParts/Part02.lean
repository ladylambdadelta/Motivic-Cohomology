import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section
open scoped BigOperators

namespace ZetaPrimePowerIndex

def heightFiber (m : ℕ) : Type :=
  {ι : ZetaPrimePowerIndex // ι ∈ heightShell m}

instance heightFiber.fintype (m : ℕ) : Fintype (heightFiber m) :=
  Finset.Subtype.fintype (heightShell m)

/-- Rectangular-height decay is pointwise nonnegative. -/
theorem polynomialHeightDecay_nonnegative
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ polynomialHeightDecay k ι := by
  unfold polynomialHeightDecay
  exact zpow_nonneg
    (add_nonneg zero_le_one (norm_nonneg ((ι.height : ℕ) : ℝ)))
    (-(k + 3 : ℤ))

/-- Rectangular-height decay is pointwise strictly positive. -/
theorem polynomialHeightDecay_pos
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 < polynomialHeightDecay k ι := by
  unfold polynomialHeightDecay
  exact zpow_pos
    (one_add_nat_norm_pos ι.height)
    (-(k + 3 : ℤ))

/-- Rectangular-height decay is bounded by one. -/
theorem polynomialHeightDecay_le_one
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    polynomialHeightDecay k ι ≤ 1 := by
  let X : ℝ := 1 + ‖((ι.height : ℕ) : ℝ)‖
  have hX_one : 1 ≤ X := by
    exact le_add_of_nonneg_right (norm_nonneg ((ι.height : ℕ) : ℝ))
  have hexp : (-(k + 3 : ℤ)) ≤ 0 := by
    exact neg_nonpos.mpr (Int.ofNat_nonneg (k + 3))
  unfold polynomialHeightDecay
  change X ^ (-(k + 3 : ℤ)) ≤ 1
  calc
    X ^ (-(k + 3 : ℤ)) ≤ X ^ (0 : ℤ) := by
      exact zpow_le_zpow_right₀ hX_one hexp
    _ = 1 := by
      exact zpow_zero X

/-- Increasing the requested polynomial decay exponent only decreases the
rectangular-height decay majorant. -/
theorem polynomialHeightDecay_le_of_le
    {k l : ℕ} (hlk : l ≤ k) (ι : ZetaPrimePowerIndex) :
    polynomialHeightDecay k ι ≤ polynomialHeightDecay l ι := by
  let X : ℝ := 1 + ‖((ι.height : ℕ) : ℝ)‖
  have hX_one : 1 ≤ X := by
    exact le_add_of_nonneg_right (norm_nonneg ((ι.height : ℕ) : ℝ))
  have hexp : (-(k + 3 : ℤ)) ≤ -(l + 3 : ℤ) := by
    have hnat : l + 3 ≤ k + 3 :=
      Nat.add_le_add_right hlk 3
    have hint : (l + 3 : ℤ) ≤ (k + 3 : ℤ) :=
      Int.ofNat_le.mpr hnat
    exact neg_le_neg hint
  unfold polynomialHeightDecay
  change X ^ (-(k + 3 : ℤ)) ≤ X ^ (-(l + 3 : ℤ))
  exact zpow_le_zpow_right₀ hX_one hexp

/-- The `tsum` over one exact-height fiber is the corresponding finite shell sum. -/
theorem tsum_heightFiber_polynomialHeightDecay_eq_shellSum
    (k m : ℕ) :
    (∑' x : heightFiber m, polynomialHeightDecay k x.1) =
      polynomialHeightShellSum k m := by
  have htsum :
      (∑' x : heightFiber m, polynomialHeightDecay k x.1) =
        ∑ x : heightFiber m, polynomialHeightDecay k x.1 :=
    tsum_fintype (fun x : heightFiber m => polynomialHeightDecay k x.1)
  have huniv :
      (∑ x : heightFiber m, polynomialHeightDecay k x.1) =
        ∑ x in (heightShell m).attach, polynomialHeightDecay k x.1 := by
    exact congrArg
      (fun s : Finset (heightFiber m) =>
        ∑ x in s, polynomialHeightDecay k x.1)
      (Finset.univ_eq_attach (heightShell m))
  have hattach :
      (∑ x in (heightShell m).attach, polynomialHeightDecay k x.1) =
        ∑ ι in heightShell m, polynomialHeightDecay k ι :=
    Finset.sum_attach
      (heightShell m)
      (fun ι : ZetaPrimePowerIndex => polynomialHeightDecay k ι)
  unfold polynomialHeightShellSum
  exact htsum.trans (huniv.trans hattach)

/-- Raw indices map constructively to their exact rectangular-height fiber. -/
def toHeightFiberSigma
    (ι : ZetaPrimePowerIndex) :
    Sigma heightFiber :=
  ⟨ι.height, ⟨ι, (mem_heightShell_iff ι.height ι).mpr rfl⟩⟩

/-- A point of a height fiber forgets to its raw prime-power index. -/
def ofHeightFiberSigma
    (s : Sigma heightFiber) : ZetaPrimePowerIndex :=
  s.2.1

/-- Forgetting after height-fiber decomposition returns the original raw index. -/
theorem ofHeightFiberSigma_toHeightFiberSigma
    (ι : ZetaPrimePowerIndex) :
    ofHeightFiberSigma (toHeightFiberSigma ι) = ι := by
  rfl

/-- Height-fiber decomposition after forgetting is the original height-fiber point. -/
theorem toHeightFiberSigma_ofHeightFiberSigma
    (s : Sigma heightFiber) :
    toHeightFiberSigma (ofHeightFiberSigma s) = s := by
  rcases s with ⟨m, x⟩
  rcases x with ⟨ι, hι⟩
  have hheight : ι.height = m :=
    (mem_heightShell_iff m ι).mp hι
  cases hheight
  rfl

/-- The constructive equivalence between raw indices and their height-fiber decomposition. -/
def heightFiberSigmaEquiv :
    ZetaPrimePowerIndex ≃ Sigma heightFiber where
  toFun := toHeightFiberSigma
  invFun := ofHeightFiberSigma
  left_inv := ofHeightFiberSigma_toHeightFiberSigma
  right_inv := toHeightFiberSigma_ofHeightFiberSigma

/-- Summability over exact-height fibers transports to summability over raw indices. -/
theorem summable_polynomialHeightDecay_of_heightFiberSummability
    (k : ℕ)
    (hshellSum : Summable (fun m : ℕ => polynomialHeightShellSum k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  have hsigma :
      Summable
        (fun s : Sigma heightFiber =>
          polynomialHeightDecay k (ofHeightFiberSigma s)) := by
    exact
      (summable_sigma_of_nonneg
        (fun s => polynomialHeightDecay_nonnegative k (ofHeightFiberSigma s))).mpr
        (And.intro
          (fun m =>
            (hasSum_fintype
              (fun x : heightFiber m => polynomialHeightDecay k x.1)).summable)
          (by
            have hfiberSums :
                (fun m : ℕ =>
                  ∑' x : heightFiber m,
                    polynomialHeightDecay k x.1) =
                  fun m : ℕ => polynomialHeightShellSum k m := by
              funext m
              exact tsum_heightFiber_polynomialHeightDecay_eq_shellSum k m
            exact Eq.subst
              (motive := fun u : ℕ → ℝ => Summable u)
              hfiberSums.symm
              hshellSum))
  exact ((heightFiberSigmaEquiv.symm).summable_iff).mp hsigma

/-- Summability of exact-height shell sums transports to summability over raw indices. -/
theorem summable_polynomialHeightDecay_of_shellSums
    (k : ℕ)
    (hshellSum : Summable (fun m : ℕ => polynomialHeightShellSum k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_heightFiberSummability k hshellSum

/-- Rectangular-height decay is summable once the height-shell masses are summable.

This is the shell-counting transport theorem from the two-dimensional raw prime-power
index to the one-dimensional height majorant. -/
theorem summable_polynomialHeightDecay_of_shellMass
    (k : ℕ)
    (hshell : Summable (fun m : ℕ => polynomialHeightShellMass k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_shellSums
    k
    (summable_polynomialHeightShellSum_of_shellMass k hshell)

/-- Rectangular-height polynomial decay is summable over raw prime-power indices. -/
theorem summable_polynomialHeightDecay
    (k : ℕ) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_shellMass
    k
    (summable_polynomialHeightShellMass k)

/-- Constant multiples of rectangular prime-power polynomial height decay are summable.

This is the combinatorial owner theorem behind contour-localization majorants.  The
exponent has two spare powers because the raw prime-power index is a rectangular
two-dimensional coordinate. -/
theorem summable_const_mul_polynomialHeightDecay
    (C : ℝ) (k : ℕ) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        C * polynomialHeightDecay k ι) := by
  exact (summable_polynomialHeightDecay k).mul_left C

/-- The completed explicit-formula prime-power weight. -/
def weight (ι : ZetaPrimePowerIndex) : ℝ :=
  if _hp : Nat.Prime ι.p then
    if _hn : 1 ≤ ι.n then
      Real.log ι.p / Real.sqrt (ι.p ^ ι.n)
    else
      0
  else
    0

/-- The square-root prime-power weight used in translation-defect packets. -/
def sqrtWeight (ι : ZetaPrimePowerIndex) : ℝ :=
  Real.sqrt (weight ι)

/-- A bounded finite window of genuine prime-power indices.  The natural bound is the owner
finite approximation; analytic cutoff statements can later compare it with a real logarithmic
height. -/
def window (N : ℕ) : Finset ZetaPrimePowerIndex :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    (fun q : ℕ × ℕ => Nat.Prime q.1 ∧ 1 ≤ q.2)
    |>.map
      ⟨fun q => ⟨q.1, q.2⟩, by
        intro q r hqr
        cases q
        cases r
        cases hqr
        rfl⟩

/-- The unfiltered rectangular box of prime-power coordinates.  Unlike `window`, this exhausts
all raw indices and is the correct object for generic `HasSum`/`tsum` exhaustion. -/
def box (N : ℕ) : Finset ZetaPrimePowerIndex :=
  rawBox N

theorem mem_box_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ box N ↔ ι.p < N + 1 ∧ ι.n < N + 1 := by
  unfold box
  exact mem_rawBox_iff N ι

/-- Rectangular raw prime-power boxes are monotone in the cutoff. -/
theorem box_mono {N M : ℕ} (hNM : N ≤ M) :
    box N ⊆ box M := by
  intro ι hι
  have hmem := (mem_box_iff N ι).mp hι
  have hp : ι.p < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.1) hNM)
  have hn : ι.n < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.2) hNM)
  exact (mem_box_iff M ι).mpr ⟨hp, hn⟩

/-- Rectangular raw prime-power boxes exhaust all raw prime-power coordinates. -/
theorem box_tendsto_atTop :
    Filter.Tendsto box Filter.atTop Filter.atTop := by
  exact Monotone.tendsto_atTop_finset
    (fun N M hNM => box_mono hNM)
    (fun ι : ZetaPrimePowerIndex =>
      ⟨max ι.p ι.n, by
        have hp_le : ι.p ≤ max ι.p ι.n := Nat.le_max_left ι.p ι.n
        have hn_le : ι.n ≤ max ι.p ι.n := Nat.le_max_right ι.p ι.n
        exact (mem_box_iff (max ι.p ι.n) ι).mpr
          ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩⟩)

theorem mem_window_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N ↔ ι.p < N + 1 ∧ ι.n < N + 1 ∧ Nat.Prime ι.p ∧ 1 ≤ ι.n := by
  constructor
  · intro hι
    unfold window at hι
    rcases Finset.mem_map.mp hι with ⟨q, hq, hqι⟩
    rcases q with ⟨p, n⟩
    have hpair :
        (p, n) ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)) ∧
          Nat.Prime p ∧ 1 ≤ n := by
      exact Finset.mem_filter.mp hq
    have hp : p < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hpair.1).1
    have hn : n < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hpair.1).2
    cases hqι
    exact ⟨hp, hn, hpair.2.1, hpair.2.2⟩
  · intro hι
    unfold window
    exact Finset.mem_map.mpr
      ⟨(ι.p, ι.n),
        Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr hι.1, Finset.mem_range.mpr hι.2.1⟩,
            hι.2.2.1, hι.2.2.2⟩,
        rfl⟩

/-- The genuine prime-power window is the genuine part of the rectangular box. -/
theorem mem_window_iff_mem_box_and_isGenuine (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N ↔ ι ∈ box N ∧ IsGenuine ι := by
  constructor
  · intro hι
    have hmem := (mem_window_iff N ι).mp hι
    exact ⟨(mem_box_iff N ι).mpr ⟨hmem.1, hmem.2.1⟩,
      ⟨hmem.2.2.1, hmem.2.2.2⟩⟩
  · intro hι
    have hbox := (mem_box_iff N ι).mp hι.1
    exact (mem_window_iff N ι).mpr
      ⟨hbox.1, hbox.2, hι.2.1, hι.2.2⟩

/-- Summing a function that vanishes on nongenuine indices over the rectangular box is the
same as summing it over the genuine prime-power window. -/
theorem sum_box_eq_sum_window_of_zero_not_isGenuine
    {A : Type*} [AddCommMonoid A]
    (a : ZetaPrimePowerIndex → A)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → a ι = 0)
    (N : ℕ) :
    ∑ ι in box N, a ι = ∑ ι in window N, a ι := by
  have hsubset : window N ⊆ box N := by
    intro ι hι
    exact ((mem_window_iff_mem_box_and_isGenuine N ι).mp hι).1
  have hsum :
      ∑ ι in window N, a ι = ∑ ι in box N, a ι := by
    exact Finset.sum_subset hsubset
      (fun ι hbox hnot_window => by
        have hnot_genuine : ¬ IsGenuine ι := by
          intro hgenuine
          exact hnot_window
            ((mem_window_iff_mem_box_and_isGenuine N ι).mpr ⟨hbox, hgenuine⟩)
        exact hzero ι hnot_genuine)
  exact hsum.symm

/-- Summable raw prime-power families are exhausted by rectangular boxes. -/
theorem tendsto_sum_box_tsum_of_summable
    (a : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable a) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in box N, a ι)
      Filter.atTop
      (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) := by
  exact hsum.hasSum.comp box_tendsto_atTop

/-- Rectangular raw prime-power boxes transport an existing complex `HasSum`. -/
theorem tendsto_sum_box_of_hasSum_complex
    (a : ZetaPrimePowerIndex → ℂ) (x : ℂ)
    (hsum : HasSum a x) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in box N, a ι)
      Filter.atTop
      (nhds x) := by
  exact hsum.comp box_tendsto_atTop

/-- Rectangular raw prime-power boxes tend to zero when the complex family has sum zero. -/
theorem tendsto_sum_box_zero_of_hasSum_complex
    (a : ZetaPrimePowerIndex → ℂ)
    (hsum : HasSum a 0) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in box N, a ι)
      Filter.atTop
      (nhds 0) := by
  exact tendsto_sum_box_of_hasSum_complex a 0 hsum

/-- Summable families that vanish on nongenuine prime-power indices are exhausted by genuine
prime-power windows. -/
theorem tendsto_sum_window_tsum_of_summable
    (a : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable a)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → a ι = 0) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in window N, a ι)
      Filter.atTop
      (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) := by
  have hbox :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in box N, a ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) :=
    tendsto_sum_box_tsum_of_summable a hsum
  have hfun :
      (fun N : ℕ => ∑ ι in box N, a ι) =
        (fun N : ℕ => ∑ ι in window N, a ι) := by
    funext N
    exact sum_box_eq_sum_window_of_zero_not_isGenuine a hzero N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Filter.Tendsto u Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, a ι)))
    hfun
    hbox

end ZetaPrimePowerIndex

end
end LFunctions
end Boundary
