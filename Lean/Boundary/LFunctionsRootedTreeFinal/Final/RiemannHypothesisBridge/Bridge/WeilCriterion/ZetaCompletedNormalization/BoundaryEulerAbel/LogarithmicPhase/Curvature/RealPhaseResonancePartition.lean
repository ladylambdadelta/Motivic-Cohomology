import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseNoWinding

/-!
# Real-phase resonance partition support

This file owns finite order lemmas used to replace global no-winding
hypotheses by resonance-aware interval decompositions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite subset of a half-open natural interval that is interval-convex is
itself a half-open interval. -/
theorem Finset.exists_eq_Ico_of_subset_Ico_intervalConvex
    {S : Finset ℕ}
    {a b : ℕ}
    (hab : a ≤ b)
    (hS_block : S ⊆ Finset.Ico a b)
    (hconvex :
      ∀ i j k : ℕ,
        i ∈ S →
        k ∈ S →
        j ∈ Finset.Ico a b →
        i ≤ j →
        j ≤ k →
          j ∈ S) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ S = Finset.Ico c d := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (Exists.intro a
          (And.intro le_rfl
            (And.intro le_rfl
              (And.intro hab
                (Eq.trans hS_empty hIco_empty.symm)))))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      let r : ℕ := S.max' hS_nonempty
      let d : ℕ := r + 1
      have hc_mem : c ∈ S :=
        Finset.min'_mem S hS_nonempty
      have hr_mem : r ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hc_block : c ∈ Finset.Ico a b :=
        hS_block hc_mem
      have hr_block : r ∈ Finset.Ico a b :=
        hS_block hr_mem
      have hc_bounds : a ≤ c ∧ c < b :=
        Finset.mem_Ico.mp hc_block
      have hr_bounds : a ≤ r ∧ r < b :=
        Finset.mem_Ico.mp hr_block
      have hc_le_r : c ≤ r :=
        Finset.min'_le S r hr_mem
      have hc_le_d : c ≤ d :=
        Nat.le_trans hc_le_r (Nat.le_succ r)
      have hd_right : d ≤ b :=
        Nat.succ_le_of_lt hr_bounds.2
      have hS_eq : S = Finset.Ico c d :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hc_le_n : c ≤ n :=
                  Finset.min'_le S n hn
                have hn_le_r : n ≤ r :=
                  Finset.le_max' S n hn
                have hn_lt_d : n < d :=
                  Nat.lt_succ_of_le hn_le_r
                Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d))
              (fun hn_interval =>
                have hn_bounds : c ≤ n ∧ n < d :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_r : n ≤ r :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Ico a b :=
                  Finset.mem_Ico.mpr
                    (And.intro
                      (Nat.le_trans hc_bounds.1 hn_bounds.1)
                      (lt_of_le_of_lt hn_le_r hr_bounds.2))
                hconvex c n r hc_mem hr_mem hn_block hn_bounds.1 hn_le_r))
      exact Exists.intro c
        (Exists.intro d
          (And.intro hc_bounds.1
            (And.intro hc_le_d
              (And.intro hd_right hS_eq))))

/-- For a monotone real sequence, the set of indices lying within a fixed
open distance from a fixed resonance center is interval-convex. -/
theorem Real.monotoneOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hmono : MonotoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam := by
  have hi_bounds :
      -lam < f i - center ∧ f i - center < lam :=
    abs_lt.mp hi_res
  have hk_bounds :
      -lam < f k - center ∧ f k - center < lam :=
    abs_lt.mp hk_res
  have hfij : f i ≤ f j :=
    hmono hi_mem hj_mem hij
  have hfjk : f j ≤ f k :=
    hmono hj_mem hk_mem hjk
  have hleft_le :
      f i - center ≤ f j - center :=
    sub_le_sub_right hfij center
  have hright_le :
      f j - center ≤ f k - center :=
    sub_le_sub_right hfjk center
  have hleft :
      -lam < f j - center :=
    lt_of_lt_of_le hi_bounds.1 hleft_le
  have hright :
      f j - center < lam :=
    lt_of_le_of_lt hright_le hk_bounds.2
  exact abs_lt.mpr (And.intro hleft hright)

/-- For an antitone real sequence, the set of indices lying within a fixed
open distance from a fixed resonance center is interval-convex. -/
theorem Real.antitoneOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hanti : AntitoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam := by
  have hi_bounds :
      -lam < f i - center ∧ f i - center < lam :=
    abs_lt.mp hi_res
  have hk_bounds :
      -lam < f k - center ∧ f k - center < lam :=
    abs_lt.mp hk_res
  have hfj_le_fi : f j ≤ f i :=
    hanti hi_mem hj_mem hij
  have hfk_le_fj : f k ≤ f j :=
    hanti hj_mem hk_mem hjk
  have hleft_le :
      f k - center ≤ f j - center :=
    sub_le_sub_right hfk_le_fj center
  have hright_le :
      f j - center ≤ f i - center :=
    sub_le_sub_right hfj_le_fi center
  have hleft :
      -lam < f j - center :=
    lt_of_lt_of_le hk_bounds.1 hleft_le
  have hright :
      f j - center < lam :=
    lt_of_le_of_lt hright_le hi_bounds.2
  exact abs_lt.mpr (And.intro hleft hright)

/-- Near-resonance sets for a sequence with a chosen monotonicity branch are
interval-convex. -/
theorem Real.monoOrAntiOn_abs_sub_lt_intervalConvex
    {f : ℕ → ℝ}
    {a b i j k : ℕ}
    {center lam : ℝ}
    (hmono_or_anti :
      MonotoneOn f (Finset.Ico a b : Set ℕ) ∨
        AntitoneOn f (Finset.Ico a b : Set ℕ))
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res : ‖f i - center‖ < lam)
    (hk_res : ‖f k - center‖ < lam) :
    ‖f j - center‖ < lam :=
  match hmono_or_anti with
  | Or.inl hmono =>
      Real.monotoneOn_abs_sub_lt_intervalConvex
        hmono hi_mem hj_mem hk_mem hij hjk hi_res hk_res
  | Or.inr hanti =>
      Real.antitoneOn_abs_sub_lt_intervalConvex
        hanti hi_mem hj_mem hk_mem hij hjk hi_res hk_res

/-- Resonance windows for a real phase with monotone adjacent increments are
interval-convex inside the adjacent-increment index block. -/
theorem Complex.realPhase_integerIncrement_resonance_intervalConvex
    (φ : ℝ → ℝ)
    {a b i j k : ℕ}
    {resonance lam : ℝ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hi_mem : i ∈ Finset.Ico a b)
    (hj_mem : j ∈ Finset.Ico a b)
    (hk_mem : k ∈ Finset.Ico a b)
    (hij : i ≤ j)
    (hjk : j ≤ k)
    (hi_res :
      ‖Complex.realPhase_integerIncrement φ i - resonance‖ < lam)
    (hk_res :
      ‖Complex.realPhase_integerIncrement φ k - resonance‖ < lam) :
    ‖Complex.realPhase_integerIncrement φ j - resonance‖ < lam :=
  Real.monoOrAntiOn_abs_sub_lt_intervalConvex
    hinc_mono hi_mem hj_mem hk_mem hij hjk hi_res hk_res

/-- A finite resonant-index set for monotone adjacent increments is a
half-open resonant window.  The set is supplied by an extensional membership
law, so this lemma does not need to manufacture decidability for the resonance
predicate. -/
theorem Complex.realPhase_integerIncrement_resonanceWindow_exists
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {resonance lam : ℝ}
    (hab : a ≤ b)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ S = Finset.Ico c d := by
  have hS_block : S ⊆ Finset.Ico a b := by
    intro n hn
    have hn_pair :
        n ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam :=
      (hS n).mp hn
    exact hn_pair.1
  have hconvex :
      ∀ i j k : ℕ,
        i ∈ S →
        k ∈ S →
        j ∈ Finset.Ico a b →
        i ≤ j →
        j ≤ k →
          j ∈ S := by
    intro i j k hi hk hj_block hij hjk
    have hi_pair :
        i ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ i - resonance‖ < lam :=
      (hS i).mp hi
    have hk_pair :
        k ∈ Finset.Ico a b ∧
          ‖Complex.realPhase_integerIncrement φ k - resonance‖ < lam :=
      (hS k).mp hk
    have hj_res :
        ‖Complex.realPhase_integerIncrement φ j - resonance‖ < lam :=
      Complex.realPhase_integerIncrement_resonance_intervalConvex
        φ hinc_mono hi_pair.1 hj_block hk_pair.1 hij hjk
        hi_pair.2 hk_pair.2
    exact (hS j).mpr (And.intro hj_block hj_res)
  exact
    Finset.exists_eq_Ico_of_subset_Ico_intervalConvex
      hab hS_block hconvex

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window, once the shifted adjacent increments are known to
be monotone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  exact
    Complex.realPhase_integerIncrement_resonanceWindow_exists
      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
      habh S hS hinc_mono

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window when the fixed-width parent gap is monotone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_parentGap_monotone
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hgap :
      MonotoneOn
        (fun n : ℕ =>
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (n + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              n)
        (Finset.Ico a (b - h) : Set ℕ)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_parentGap_monotone
      t hgap
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- A finite resonant-index set for a shifted logarithmic difference is a
half-open resonant window when the fixed-width parent gap is antitone. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_parentGap_antitone
    (t : ℝ)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam)
    (hgap :
      AntitoneOn
        (fun n : ℕ =>
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (n + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              n)
        (Finset.Ico a (b - h) : Set ℕ)) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_parentGap_antitone
      t hgap
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- In the nonnegative-frequency branch, every finite resonant-index set for a
shifted logarithmic difference is a half-open resonant window. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {resonance lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (S : Finset ℕ)
    (hS :
      ∀ n : ℕ,
        n ∈ S ↔
          n ∈ Finset.Ico a (b - h) ∧
            ‖Complex.realPhase_integerIncrement
                (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
              resonance‖ < lam) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S = Finset.Ico c d := by
  have hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
      t ht_nonneg ha
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists
      t habh S hS hinc_mono

/-- A family of finite resonant-index sets for a shifted logarithmic
difference consists pointwise of half-open resonant windows in the
nonnegative-frequency branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_family_exists_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (S : ℤ → Finset ℕ)
    (hS :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ S k ↔
            n ∈ Finset.Ico a (b - h) ∧
              ‖Complex.realPhase_integerIncrement
                  (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n -
                (2 * Real.pi * (k : ℝ))‖ < lam) :
    ∀ k : ℤ,
      ∃ c d : ℕ,
        a ≤ c ∧ c ≤ d ∧ d ≤ b - h ∧ S k = Finset.Ico c d := by
  intro k
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_exists_of_nonneg
      t ht_nonneg ha habh (S k) (hS k)

/-- Outside an extensionally specified resonant-index set, the adjacent
increment is separated from that resonance. -/
theorem Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hn_block : n ∈ Finset.Ico a b)
    (hn_not_mem : n ∉ S) :
    lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ := by
  have hn_not_lt :
      ¬ ‖Complex.realPhase_integerIncrement φ n - resonance‖ < lam := by
    intro hn_lt
    have hn_mem : n ∈ S :=
      (hS n).mpr (And.intro hn_block hn_lt)
    exact hn_not_mem hn_mem
  exact le_of_not_gt hn_not_lt

/-- A subblock avoiding an extensionally specified resonant window is pointwise
separated from the corresponding resonance center. -/
theorem Complex.realPhase_integerIncrement_separated_from_resonance_on_subblock
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S) :
    ∀ n : ℕ,
      n ∈ Finset.Ico c d →
        lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ := by
  intro n hn
  exact
    Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
      φ S hS (hsub hn) (havoid n hn)

/-- A subblock avoiding the resonant window supplies the standard separated
increment hypothesis on that subblock. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hresonance_eq :
      resonance = 2 * Real.pi * (0 : ℝ))
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S)
    (honly_zero :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          ∀ k : ℤ,
            ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (0 : ℝ))‖ ≤
              ‖Complex.realPhase_integerIncrement φ n -
                (2 * Real.pi * (k : ℝ))‖) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  have hzero_sep :
      lam ≤
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (0 : ℝ))‖ := by
    have hres_sep :
        lam ≤ ‖Complex.realPhase_integerIncrement φ n - resonance‖ :=
      Complex.realPhase_integerIncrement_separated_from_resonance_on_subblock
        φ S hS hsub havoid n hn
    exact
      Eq.subst
        (motive := fun r : ℝ =>
          lam ≤ ‖Complex.realPhase_integerIncrement φ n - r‖)
        hresonance_eq
        hres_sep
  exact le_trans hzero_sep (honly_zero n hn k)

/-- A subblock avoiding the resonant window supplies separated increments when
principal-interval control makes the zero lattice center the closest center. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance_principal
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {resonance lam : ℝ}
    (S : Finset ℕ)
    (hresonance_eq :
      resonance = 2 * Real.pi * (0 : ℝ))
    (hS :
      ∀ m : ℕ,
        m ∈ S ↔
          m ∈ Finset.Ico a b ∧
            ‖Complex.realPhase_integerIncrement φ m - resonance‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid : ∀ n : ℕ, n ∈ Finset.Ico c d → n ∉ S)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  exact
    Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_avoidance
      φ S hresonance_eq hS hsub havoid
      (fun n hn k =>
        Complex.realPhase_integerIncrement_zero_lattice_closest_of_mem_principal
          φ (hprincipal n hn) k)

/-- Avoidance of the resonance window around every integer lattice center
supplies the standard separated-increment hypothesis without any principal
interval or no-winding assumption. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_of_resonanceWindow_family_avoidance
    (φ : ℝ → ℝ)
    {a b c d : ℕ}
    {lam : ℝ}
    (S : ℤ → Finset ℕ)
    (hS :
      ∀ k : ℤ,
        ∀ m : ℕ,
          m ∈ S k ↔
            m ∈ Finset.Ico a b ∧
              ‖Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ))‖ < lam)
    (hsub : Finset.Ico c d ⊆ Finset.Ico a b)
    (havoid :
      ∀ k : ℤ,
        ∀ n : ℕ,
          n ∈ Finset.Ico c d →
            n ∉ S k) :
    Complex.realPhase_integerIncrementSeparatedOn φ c d lam := by
  intro n hn k
  exact
    Complex.realPhase_integerIncrement_separated_from_resonance_of_not_mem_window
      φ (S k) (hS k) (hsub hn) (havoid k n hn)

end

end LFunctions
end Boundary
