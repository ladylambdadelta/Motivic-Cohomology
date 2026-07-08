import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Active resonance cover support

This file owns bounded finite-cover and active-center counting refinements for
the resonance partition owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Every interval in a gap family lies inside a fixed ambient half-open block. -/
def Complex.realPhase_IcoFamilyBounded
    (a b : ℕ)
    (gaps : Finset (ℕ × ℕ)) : Prop :=
  ∀ p : ℕ × ℕ, p ∈ gaps → a ≤ p.1 ∧ p.2 ≤ b


/-- The singleton ambient gap family is bounded by its ambient block. -/
theorem Complex.realPhase_IcoFamilyBounded_singleton
    {a b : ℕ}
    (_hab : a ≤ b) :
    Complex.realPhase_IcoFamilyBounded a b
      (Finset.singleton (a, b)) := by
  intro p hp
  have hp_eq : p = (a, b) :=
    Finset.mem_singleton.mp hp
  have hp_bounds : a ≤ (a, b).1 ∧ (a, b).2 ≤ b :=
    And.intro le_rfl le_rfl
  exact
    Eq.subst
      (motive := fun q : ℕ × ℕ => a ≤ q.1 ∧ q.2 ≤ b)
      hp_eq.symm
      hp_bounds


/-- Splitting one gap by a contained half-open interval preserves ambient
endpoint bounds for the gap family. -/
theorem Complex.realPhase_IcoFamily_splitGapAtIco_bounded
    (gaps : Finset (ℕ × ℕ))
    {p : ℕ × ℕ}
    {a b c d : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c ≤ d)
    (hdp : d ≤ p.2)
    (hbounded : Complex.realPhase_IcoFamilyBounded a b gaps) :
    Complex.realPhase_IcoFamilyBounded a b
      (Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d) := by
  intro q hq
  have hq_cases :
      q ∈ gaps.erase p ∨ q ∈ Nat.IcoTwoGapComplement p.1 p.2 c d :=
    Finset.mem_union.mp hq
  match hq_cases with
  | Or.inl hq_erase =>
      have hq_old : q ∈ gaps :=
        (Finset.mem_erase.mp hq_erase).2
      exact hbounded q hq_old
  | Or.inr hq_two =>
      have hp_bounds : a ≤ p.1 ∧ p.2 ≤ b :=
        hbounded p hp
      have hq_two_cases :
          q = (p.1, c) ∨ q ∈ Finset.singleton (d, p.2) :=
        Finset.mem_insert.mp hq_two
      match hq_two_cases with
      | Or.inl hq_left =>
          exact
            Eq.subst
              (motive := fun r : ℕ × ℕ => a ≤ r.1 ∧ r.2 ≤ b)
              hq_left.symm
              (And.intro hp_bounds.1
                (Nat.le_trans hcd (Nat.le_trans hdp hp_bounds.2)))
      | Or.inr hq_right_mem =>
          have hq_right : q = (d, p.2) :=
            Finset.mem_singleton.mp hq_right_mem
          exact
            Eq.subst
              (motive := fun r : ℕ × ℕ => a ≤ r.1 ∧ r.2 ≤ b)
              hq_right.symm
              (And.intro
                (Nat.le_trans hp_bounds.1 (Nat.le_trans hpc hcd))
                hp_bounds.2)


/-- Bounded one-step package for removing one nonempty contained half-open
interval while preserving disjointness, interval-connectedness, and ambient
endpoint bounds. -/
theorem Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_of_splitGapAtIco_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {p : ℕ × ℕ}
    {a b c d budget : ℕ}
    (hp : p ∈ gaps)
    (hpc : p.1 ≤ c)
    (hcd : c < d)
    (hdp : d ≤ p.2)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hbounded : Complex.realPhase_IcoFamilyBounded a b gaps)
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        Complex.realPhase_IcoFamilyBounded a b newGaps ∧
        newGaps.card ≤ budget + 1 := by
  let newGaps : Finset (ℕ × ℕ) :=
    Complex.realPhase_IcoFamily_splitGapAtIco gaps p c d
  have hcd_le : c ≤ d :=
    le_of_lt hcd
  have hsplit_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        (Complex.realPhase_IcoFamilyUnion gaps).filter
          (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Complex.realPhase_IcoFamilyUnion_splitGapAtIco_eq_filter_not_Ico
      gaps hp hpc hcd_le hdp hdisjoint
  have htarget_cover :
      Complex.realPhase_IcoFamilyUnion newGaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hsplit_cover
      (congrArg
        (fun U : Finset ℕ =>
          U.filter (fun n : ℕ => n ∉ Finset.Ico c d))
        hcover)
  have hnew_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ newGaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ newGaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2) :=
    Complex.realPhase_IcoFamily_splitGapAtIco_pairwiseDisjoint
      gaps hp hpc hcd_le hdp hdisjoint
  have hnew_connected :
      Complex.realPhase_IcoFamilyIntervalConnected newGaps :=
    Complex.realPhase_IcoFamily_splitGapAtIco_intervalConnected
      gaps hp hpc hcd hdp hdisjoint hconnected
  have hnew_bounded :
      Complex.realPhase_IcoFamilyBounded a b newGaps :=
    Complex.realPhase_IcoFamily_splitGapAtIco_bounded
      gaps hp hpc hcd_le hdp hbounded
  have hnew_card_to_gaps :
      newGaps.card ≤ gaps.card + 1 :=
    Complex.realPhase_IcoFamily_splitGapAtIco_card_le_succ
      gaps hp c d
  have hbudget_step :
      gaps.card + 1 ≤ budget + 1 :=
    add_le_add_right hcard 1
  have hnew_card :
      newGaps.card ≤ budget + 1 :=
    le_trans hnew_card_to_gaps hbudget_step
  exact Exists.intro newGaps
    (And.intro htarget_cover
      (And.intro hnew_disjoint
        (And.intro hnew_connected
          (And.intro hnew_bounded hnew_card))))

/-- Removing an empty half-open interval preserves the bounded connected cover
package unchanged. -/
theorem Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_of_empty_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {a b c d budget : ℕ}
    (hdc : d ≤ c)
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hbounded : Complex.realPhase_IcoFamilyBounded a b gaps)
    (hcard : gaps.card ≤ budget) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        Complex.realPhase_IcoFamilyBounded a b newGaps ∧
        newGaps.card ≤ budget := by
  have hfilter_eq :
      S.filter (fun n : ℕ => n ∉ Finset.Ico c d) = S := by
    exact Finset.ext
      (fun n =>
        Iff.intro
          (fun hn => (Finset.mem_filter.mp hn).1)
          (fun hn =>
            have hn_not : n ∉ Finset.Ico c d := by
              intro hn_cd
              have hn_bounds : c ≤ n ∧ n < d :=
                Finset.mem_Ico.mp hn_cd
              have hd_le_n : d ≤ n :=
                Nat.le_trans hdc hn_bounds.1
              exact not_lt_of_ge hd_le_n hn_bounds.2
            Finset.mem_filter.mpr (And.intro hn hn_not)))
  have htarget :
      Complex.realPhase_IcoFamilyUnion gaps =
        S.filter (fun n : ℕ => n ∉ Finset.Ico c d) :=
    Eq.trans hcover hfilter_eq.symm
  exact Exists.intro gaps
    (And.intro htarget
      (And.intro hdisjoint
        (And.intro hconnected
          (And.intro hbounded hcard))))

/-- One bounded induction step for removing a whole half-open interval from an
interval-connected gap cover. -/
theorem Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_step_budget
    {S : Finset ℕ}
    {gaps : Finset (ℕ × ℕ)}
    {a b c d budget : ℕ}
    (hcover : Complex.realPhase_IcoFamilyUnion gaps = S)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hconnected :
      Complex.realPhase_IcoFamilyIntervalConnected gaps)
    (hbounded : Complex.realPhase_IcoFamilyBounded a b gaps)
    (hcard : gaps.card ≤ budget)
    (hwindow_subset : Finset.Ico c d ⊆ S) :
    ∃ newGaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion newGaps =
          S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ newGaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ newGaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
        Complex.realPhase_IcoFamilyBounded a b newGaps ∧
        newGaps.card ≤ budget + 1 := by
  match lt_or_ge c d with
  | Or.inr hdc =>
      have hsame :
          ∃ newGaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion newGaps =
                S.filter (fun n : ℕ => n ∉ Finset.Ico c d) ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ newGaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ newGaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
              Complex.realPhase_IcoFamilyBounded a b newGaps ∧
              newGaps.card ≤ budget :=
        Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_of_empty_budget
          hdc hcover hdisjoint hconnected hbounded hcard
      match hsame with
      | ⟨newGaps, hcover_new, hdisjoint_new, hconnected_new,
          hbounded_new, hcard_new⟩ =>
          have hcard_succ : newGaps.card ≤ budget + 1 :=
            le_trans hcard_new (Nat.le_succ budget)
          exact Exists.intro newGaps
            (And.intro hcover_new
              (And.intro hdisjoint_new
                (And.intro hconnected_new
                  (And.intro hbounded_new hcard_succ))))
  | Or.inl hcd =>
      have hwindow_union :
          Finset.Ico c d ⊆ Complex.realPhase_IcoFamilyUnion gaps := by
        intro n hn
        have hnS : n ∈ S :=
          hwindow_subset hn
        exact
          Eq.subst
            (motive := fun U : Finset ℕ => n ∈ U)
            hcover.symm
            hnS
      have hp_exists :
          ∃ p : ℕ × ℕ,
            p ∈ gaps ∧ Finset.Ico c d ⊆ Finset.Ico p.1 p.2 :=
        hconnected hwindow_union hcd
      match hp_exists with
      | ⟨p, hp, hp_contains⟩ =>
          have hbounds :
              p.1 ≤ c ∧ d ≤ p.2 :=
            Nat.Ico_endpoint_bounds_of_subset_of_nonempty
              hp_contains hcd
          exact
            Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_of_splitGapAtIco_budget
              hp hbounds.1 hcd hbounds.2 hcover hdisjoint
              hconnected hbounded hcard


/-- Bounded form of the finite integer-centered resonance-family complement
cover.  Every gap interval remains inside the ambient block. -/
theorem Complex.exists_bounded_IcoFamily_connected_cover_resonanceFamilyComplement_of_window_eq_of_le_pi
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ)
    (K : Finset ℤ)
    (hab : a ≤ b)
    (hlam : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        Complex.realPhase_IcoFamilyBounded a b gaps ∧
        gaps.card ≤ K.card + 1 := by
  have hind :
      (∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d) →
        ∃ gaps : Finset (ℕ × ℕ),
          Complex.realPhase_IcoFamilyUnion gaps =
              Complex.realPhase_integerIncrementResonanceFamilyComplement
                φ a b lam K ∧
            (∀ p₁ : ℕ × ℕ,
              p₁ ∈ gaps →
                ∀ p₂ : ℕ × ℕ,
                  p₂ ∈ gaps →
                    p₁ ≠ p₂ →
                      Disjoint (Finset.Ico p₁.1 p₁.2)
                        (Finset.Ico p₂.1 p₂.2)) ∧
            Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
            Complex.realPhase_IcoFamilyBounded a b gaps ∧
            gaps.card ≤ K.card + 1 :=
    Finset.induction_on K
    (fun _hwindow_empty => by
      let gaps : Finset (ℕ × ℕ) := Finset.singleton (a, b)
      have hcover_Ico :
          Complex.realPhase_IcoFamilyUnion gaps = Finset.Ico a b :=
        Complex.realPhase_IcoFamilyUnion_singleton a b
      have hcomplement_empty :
          Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam (∅ : Finset ℤ) =
            Finset.Ico a b :=
        Complex.realPhase_integerIncrementResonanceFamilyComplement_empty
          φ a b lam
      have hcover :
          Complex.realPhase_IcoFamilyUnion gaps =
            Complex.realPhase_integerIncrementResonanceFamilyComplement
              φ a b lam (∅ : Finset ℤ) :=
        Eq.trans hcover_Ico hcomplement_empty.symm
      have hdisjoint :
          ∀ p₁ : ℕ × ℕ,
            p₁ ∈ gaps →
              ∀ p₂ : ℕ × ℕ,
                p₂ ∈ gaps →
                  p₁ ≠ p₂ →
                    Disjoint (Finset.Ico p₁.1 p₁.2)
                      (Finset.Ico p₂.1 p₂.2) := by
        intro p₁ hp₁ p₂ hp₂ hpne
        have hp₁_eq : p₁ = (a, b) :=
          Finset.mem_singleton.mp hp₁
        have hp₂_eq : p₂ = (a, b) :=
          Finset.mem_singleton.mp hp₂
        have hp_eq : p₁ = p₂ :=
          Eq.trans hp₁_eq hp₂_eq.symm
        exact False.elim (hpne hp_eq)
      have hconnected :
          Complex.realPhase_IcoFamilyIntervalConnected gaps :=
        Complex.realPhase_IcoFamilyIntervalConnected_singleton a b
      have hbounded :
          Complex.realPhase_IcoFamilyBounded a b gaps :=
        Complex.realPhase_IcoFamilyBounded_singleton hab
      have hcard_one : gaps.card = 1 :=
        Finset.card_singleton (a, b)
      have hcard : gaps.card ≤ (∅ : Finset ℤ).card + 1 := by
        have hzero_add : (∅ : Finset ℤ).card + 1 = 1 :=
          congrArg (fun n : ℕ => n + 1) Finset.card_empty
        exact
          Eq.subst
            (motive := fun right : ℕ => gaps.card ≤ right)
            hzero_add.symm
            (le_of_eq hcard_one)
      exact Exists.intro gaps
        (And.intro hcover
          (And.intro hdisjoint
            (And.intro hconnected
              (And.intro hbounded hcard)))))
    (fun k K hk_not ih hwindow_insert => by
      have hwindow_old :
          ∀ j : ℤ,
            j ∈ K →
              ∃ c d : ℕ,
                Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (j : ℝ)) lam =
                  Finset.Ico c d := by
        intro j hj
        exact hwindow_insert j (Finset.mem_insert_of_mem hj)
      have ih_data :
          ∃ gaps : Finset (ℕ × ℕ),
            Complex.realPhase_IcoFamilyUnion gaps =
                Complex.realPhase_integerIncrementResonanceFamilyComplement
                  φ a b lam K ∧
              (∀ p₁ : ℕ × ℕ,
                p₁ ∈ gaps →
                  ∀ p₂ : ℕ × ℕ,
                    p₂ ∈ gaps →
                      p₁ ≠ p₂ →
                        Disjoint (Finset.Ico p₁.1 p₁.2)
                          (Finset.Ico p₂.1 p₂.2)) ∧
              Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
              Complex.realPhase_IcoFamilyBounded a b gaps ∧
              gaps.card ≤ K.card + 1 :=
        ih hwindow_old
      match ih_data with
      | ⟨gaps, hcover, hdisjoint, hconnected, hbounded, hcard⟩ =>
          have hk_mem_insert : k ∈ insert k K :=
            Finset.mem_insert_self k K
          have hwindow_k_exists :
              ∃ c d : ℕ,
                Complex.realPhase_integerIncrementResonanceWindow
                    φ a b (2 * Real.pi * (k : ℝ)) lam =
                  Finset.Ico c d :=
            hwindow_insert k hk_mem_insert
          match hwindow_k_exists with
          | ⟨c, d, hwindow_k⟩ =>
              have hwindow_subset :
                  Finset.Ico c d ⊆
                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                      φ a b lam K :=
                Complex.Ico_subset_resonanceFamilyComplement_of_window_eq_of_not_mem_of_le_pi
                  φ hlam hk_not hwindow_k
              have hstep :
                  ∃ newGaps : Finset (ℕ × ℕ),
                    Complex.realPhase_IcoFamilyUnion newGaps =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ => n ∉ Finset.Ico c d) ∧
                      (∀ p₁ : ℕ × ℕ,
                        p₁ ∈ newGaps →
                          ∀ p₂ : ℕ × ℕ,
                            p₂ ∈ newGaps →
                              p₁ ≠ p₂ →
                                Disjoint (Finset.Ico p₁.1 p₁.2)
                                  (Finset.Ico p₂.1 p₂.2)) ∧
                      Complex.realPhase_IcoFamilyIntervalConnected newGaps ∧
                      Complex.realPhase_IcoFamilyBounded a b newGaps ∧
                      newGaps.card ≤ (K.card + 1) + 1 :=
                Complex.exists_bounded_IcoFamily_connected_cover_filter_not_Ico_step_budget
                  hcover hdisjoint hconnected hbounded hcard hwindow_subset
              match hstep with
              | ⟨newGaps, hcover_step, hdisjoint_new,
                  hconnected_new, hbounded_new, hcard_step⟩ =>
                  have hfilter_window :
                      (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ => n ∉ Finset.Ico c d) =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ =>
                            n ∉
                              Complex.realPhase_integerIncrementResonanceWindow
                                φ a b (2 * Real.pi * (k : ℝ)) lam) := by
                    exact Finset.ext
                      (fun n =>
                        Iff.intro
                          (fun hn =>
                            have hdata :
                                n ∈
                                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                                      φ a b lam K ∧
                                  n ∉ Finset.Ico c d :=
                              Finset.mem_filter.mp hn
                            have hn_not_window :
                                n ∉
                                  Complex.realPhase_integerIncrementResonanceWindow
                                    φ a b (2 * Real.pi * (k : ℝ)) lam := by
                              intro hn_window
                              have hn_Ico : n ∈ Finset.Ico c d :=
                                Eq.subst
                                  (motive := fun S : Finset ℕ => n ∈ S)
                                  hwindow_k
                                  hn_window
                              exact hdata.2 hn_Ico
                            Finset.mem_filter.mpr
                              (And.intro hdata.1 hn_not_window))
                          (fun hn =>
                            have hdata :
                                n ∈
                                    Complex.realPhase_integerIncrementResonanceFamilyComplement
                                      φ a b lam K ∧
                                  n ∉
                                    Complex.realPhase_integerIncrementResonanceWindow
                                      φ a b (2 * Real.pi * (k : ℝ)) lam :=
                              Finset.mem_filter.mp hn
                            have hn_not_Ico : n ∉ Finset.Ico c d := by
                              intro hn_Ico
                              have hn_window :
                                  n ∈
                                    Complex.realPhase_integerIncrementResonanceWindow
                                      φ a b (2 * Real.pi * (k : ℝ)) lam :=
                                Eq.subst
                                  (motive := fun S : Finset ℕ => n ∈ S)
                                  hwindow_k.symm
                                  hn_Ico
                              exact hdata.2 hn_window
                            Finset.mem_filter.mpr
                              (And.intro hdata.1 hn_not_Ico)))
                  have hinsert_complement :
                      Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam (insert k K) =
                        (Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam K).filter
                          (fun n : ℕ =>
                            n ∉
                              Complex.realPhase_integerIncrementResonanceWindow
                                φ a b (2 * Real.pi * (k : ℝ)) lam) :=
                    Complex.realPhase_integerIncrementResonanceFamilyComplement_insert
                      φ a b lam k K
                  have hcover_new :
                      Complex.realPhase_IcoFamilyUnion newGaps =
                        Complex.realPhase_integerIncrementResonanceFamilyComplement
                          φ a b lam (insert k K) :=
                    Eq.trans hcover_step
                      (Eq.trans hfilter_window hinsert_complement.symm)
                  have hinsert_card :
                      (insert k K).card = K.card + 1 :=
                    Finset.card_insert_of_not_mem hk_not
                  have hcard_new :
                      newGaps.card ≤ (insert k K).card + 1 :=
                    Eq.subst
                      (motive := fun m : ℕ => newGaps.card ≤ m + 1)
                      hinsert_card.symm
                      hcard_step
                  exact Exists.intro newGaps
                    (And.intro hcover_new
                      (And.intro hdisjoint_new
                        (And.intro hconnected_new
                          (And.intro hbounded_new hcard_new)))))
  exact hind hwindow


/-- If one sample increment lies in an a priori range, then its padded
sample-active center interval is contained in the corresponding range-active
center interval. -/
theorem Complex.realPhase_integerIncrementSampleActiveCenters_subset_rangeActiveCenters_of_range
    (φ : ℝ → ℝ)
    {lo hi lam : ℝ}
    {n : ℕ}
    (hlo :
      lo ≤ Complex.realPhase_integerIncrement φ n)
    (hhi :
      Complex.realPhase_integerIncrement φ n ≤ hi) :
    Complex.realPhase_integerIncrementSampleActiveCenters φ lam n ⊆
      Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  intro k hk
  let θ : ℝ := Complex.realPhase_integerIncrement φ n
  have htheta :
      θ = Complex.realPhase_integerIncrement φ n :=
    Eq.refl θ
  have hloθ : lo ≤ θ :=
    Eq.subst
      (motive := fun r : ℝ => lo ≤ r)
      htheta.symm
      hlo
  have hθhi : θ ≤ hi :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ hi)
      htheta.symm
      hhi
  have hk_bounds :
      ⌊((Complex.realPhase_integerIncrement φ n - lam) /
          (2 * Real.pi))⌋ - 1 ≤ k ∧
        k ≤
          ⌊((Complex.realPhase_integerIncrement φ n + lam) /
            (2 * Real.pi))⌋ + 1 :=
    Finset.mem_Icc.mp hk
  have hleft_arg :
      ((lo - lam) / (2 * Real.pi)) ≤ ((θ - lam) / (2 * Real.pi)) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hloθ lam)
      (le_of_lt Real.two_pi_pos)
  have hleft_floor :
      ⌊((lo - lam) / (2 * Real.pi))⌋ ≤
        ⌊((θ - lam) / (2 * Real.pi))⌋ :=
    Int.floor_mono hleft_arg
  have hleft_floor_shift :
      ⌊((lo - lam) / (2 * Real.pi))⌋ - 1 ≤
        ⌊((θ - lam) / (2 * Real.pi))⌋ - 1 :=
    sub_le_sub_right hleft_floor 1
  have hleft_sample :
      ⌊((θ - lam) / (2 * Real.pi))⌋ - 1 ≤ k :=
    Eq.subst
      (motive := fun r : ℝ =>
        ⌊((r - lam) / (2 * Real.pi))⌋ - 1 ≤ k)
      htheta
      hk_bounds.1
  have hleft :
      ⌊((lo - lam) / (2 * Real.pi))⌋ - 1 ≤ k :=
    le_trans hleft_floor_shift hleft_sample
  have hright_arg :
      ((θ + lam) / (2 * Real.pi)) ≤ ((hi + lam) / (2 * Real.pi)) :=
    div_le_div_of_nonneg_right (add_le_add_right hθhi lam)
      (le_of_lt Real.two_pi_pos)
  have hright_floor :
      ⌊((θ + lam) / (2 * Real.pi))⌋ ≤
        ⌊((hi + lam) / (2 * Real.pi))⌋ :=
    Int.floor_mono hright_arg
  have hright_floor_shift :
      ⌊((θ + lam) / (2 * Real.pi))⌋ + 1 ≤
        ⌊((hi + lam) / (2 * Real.pi))⌋ + 1 :=
    add_le_add_right hright_floor 1
  have hright_sample :
      k ≤ ⌊((θ + lam) / (2 * Real.pi))⌋ + 1 :=
    Eq.subst
      (motive := fun r : ℝ =>
        k ≤ ⌊((r + lam) / (2 * Real.pi))⌋ + 1)
      htheta
      hk_bounds.2
  have hright :
      k ≤ ⌊((hi + lam) / (2 * Real.pi))⌋ + 1 :=
    le_trans hright_sample hright_floor_shift
  exact Finset.mem_Icc.mpr (And.intro hleft hright)

/-- If all sample increments in a block lie in an a priori range, then the
samplewise active-center family is contained in the single range-active
integer-center interval. -/
theorem Complex.realPhase_integerIncrementActiveCenters_subset_rangeActiveCenters_of_range
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lo hi lam : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi) :
    Complex.realPhase_integerIncrementActiveCenters φ a b lam ⊆
      Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam := by
  intro k hk
  have hk_data :
      ∃ n : ℕ,
        n ∈ Finset.Ico a b ∧
          k ∈ Complex.realPhase_integerIncrementSampleActiveCenters φ lam n :=
    Finset.mem_biUnion.mp hk
  match hk_data with
  | ⟨n, hn, hk_sample⟩ =>
      have hn_range :
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi :=
        hrange n hn
      exact
        Complex.realPhase_integerIncrementSampleActiveCenters_subset_rangeActiveCenters_of_range
          φ hn_range.1 hn_range.2 hk_sample

/-- Cardinality bound for the samplewise active-center family by the single
range-active center interval. -/
theorem Complex.realPhase_integerIncrementActiveCenters_card_le_rangeActiveCenters_card_of_range
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lo hi lam : ℝ}
    (hrange :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lo ≤ Complex.realPhase_integerIncrement φ n ∧
            Complex.realPhase_integerIncrement φ n ≤ hi) :
    (Complex.realPhase_integerIncrementActiveCenters φ a b lam).card ≤
      (Complex.realPhase_integerIncrementRangeActiveCenters lo hi lam).card := by
  exact Finset.card_le_card
    (Complex.realPhase_integerIncrementActiveCenters_subset_rangeActiveCenters_of_range
      φ hrange)


/-- Bounded monotone-increment form of the finite integer-centered
resonance-family complement cover. -/
theorem Complex.exists_bounded_IcoFamily_connected_cover_resonanceFamilyComplement_of_mono_of_le_pi
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (K : Finset ℤ)
    (hab : a ≤ b)
    (hmono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hlam : lam ≤ Real.pi) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.realPhase_integerIncrementResonanceFamilyComplement
            φ a b lam K ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        Complex.realPhase_IcoFamilyBounded a b gaps ∧
        gaps.card ≤ K.card + 1 := by
  have hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                φ a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d := by
    intro k _hk
    have hcanonical :
        ∃ c d : ℕ,
          a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
            Complex.realPhase_integerIncrementResonanceWindow
              φ a b (2 * Real.pi * (k : ℝ)) lam =
                Finset.Ico c d :=
      Complex.realPhase_integerIncrement_resonanceWindow_exists_canonical
        φ hab hmono
    match hcanonical with
    | ⟨c, d, _hac, _hcd, _hdb, hwindow_eq⟩ =>
        exact Exists.intro c (Exists.intro d hwindow_eq)
  exact
    Complex.exists_bounded_IcoFamily_connected_cover_resonanceFamilyComplement_of_window_eq_of_le_pi
      φ a b lam K hab hlam hwindow


/-- Shifted-logarithmic active-center complements have bounded disjoint
interval-connected gap covers with at most one more gap than the number of
active integer centers. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_activeComplement_exists_bounded_IcoFamily_cover_of_mono_of_le_pi
    (t : ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (habh : a ≤ b - h)
    (hmono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hlam : lam ≤ Real.pi) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeResonanceComplement
            t a b h lam ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        Complex.realPhase_IcoFamilyBounded a (b - h) gaps ∧
        gaps.card ≤
          (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h lam).card + 1 := by
  exact
    Complex.exists_bounded_IcoFamily_connected_cover_resonanceFamilyComplement_of_mono_of_le_pi
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
        t a b h lam)
      habh hmono hlam

end

end LFunctions
end Boundary
