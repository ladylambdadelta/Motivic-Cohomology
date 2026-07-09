import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Additive principal-strip refinement

This file owns the finite combinatorial step in the monotone-curvature
all-integer resonance decomposition: refining monotone resonance-family gaps by
principal integer strips costs additively in the number of strip crossings.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Filtering one half-open interval by membership in another gives the
half-open interval with max/min endpoints. -/
theorem Nat.Ico_filter_mem_Ico_eq_Ico_max_min
    (p r : ℕ × ℕ) :
    (Finset.Ico p.1 p.2).filter
        (fun n : ℕ => n ∈ Finset.Ico r.1 r.2) =
      Finset.Ico (max p.1 r.1) (min p.2 r.2) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hp : n ∈ Finset.Ico p.1 p.2 :=
            (Finset.mem_filter.mp hn).1
          have hr : n ∈ Finset.Ico r.1 r.2 :=
            (Finset.mem_filter.mp hn).2
          have hp_bounds : p.1 ≤ n ∧ n < p.2 :=
            Finset.mem_Ico.mp hp
          have hr_bounds : r.1 ≤ n ∧ n < r.2 :=
            Finset.mem_Ico.mp hr
          have hleft : max p.1 r.1 ≤ n :=
            max_le hp_bounds.1 hr_bounds.1
          have hright : n < min p.2 r.2 :=
            lt_min hp_bounds.2 hr_bounds.2
          Finset.mem_Ico.mpr (And.intro hleft hright))
        (fun hn =>
          have hbounds : max p.1 r.1 ≤ n ∧ n < min p.2 r.2 :=
            Finset.mem_Ico.mp hn
          have hp_left : p.1 ≤ n :=
            le_trans (Nat.le_max_left p.1 r.1) hbounds.1
          have hp_right : n < p.2 :=
            lt_of_lt_of_le hbounds.2 (Nat.min_le_left p.2 r.2)
          have hr_left : r.1 ≤ n :=
            le_trans (Nat.le_max_right p.1 r.1) hbounds.1
          have hr_right : n < r.2 :=
            lt_of_lt_of_le hbounds.2 (Nat.min_le_right p.2 r.2)
          Finset.mem_filter.mpr
            (And.intro
              (Finset.mem_Ico.mpr (And.intro hp_left hp_right))
              (Finset.mem_Ico.mpr (And.intro hr_left hr_right)))))

/-- The raw finite intersection family used in the additive sweep. -/
def Complex.realPhase_IcoFamily_pairwiseIntersections
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (left.product K).image
    (fun pk : (ℕ × ℕ) × ℤ =>
      (max pk.1.1 (right pk.2).1, min pk.1.2 (right pk.2).2))

/-- Nonempty pairwise intersections have the expected union. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_union_eq
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ) :
    Complex.realPhase_IcoFamilyUnion
        ((Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)) =
      (Complex.realPhase_IcoFamilyUnion left).filter
        (fun n : ℕ =>
          n ∈ Complex.realPhase_IcoFamilyUnion (K.image right)) := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_union :
              ∃ q : ℕ × ℕ,
                q ∈
                  (Complex.realPhase_IcoFamily_pairwiseIntersections
                    left K right).filter
                    (fun q : ℕ × ℕ => q.1 < q.2) ∧
                  n ∈ Finset.Ico q.1 q.2 :=
            Finset.mem_biUnion.mp hn
          match hn_union with
          | ⟨q, hq, hnq⟩ =>
              have hq_image :
                  q ∈
                    Complex.realPhase_IcoFamily_pairwiseIntersections
                      left K right :=
                (Finset.mem_filter.mp hq).1
              have hpre :
                  ∃ pk : (ℕ × ℕ) × ℤ,
                    pk ∈ left.product K ∧
                      (fun pk : (ℕ × ℕ) × ℤ =>
                        (max pk.1.1 (right pk.2).1,
                          min pk.1.2 (right pk.2).2)) pk = q :=
                Finset.mem_image.mp hq_image
              match hpre with
              | ⟨pk, hpk, hpkq⟩ =>
                  have hp_mem : pk.1 ∈ left :=
                    (Finset.mem_product.mp hpk).1
                  have hk_mem : pk.2 ∈ K :=
                    (Finset.mem_product.mp hpk).2
                  have hn_component :
                      n ∈ Finset.Ico
                        (max pk.1.1 (right pk.2).1)
                        (min pk.1.2 (right pk.2).2) :=
                    Eq.subst
                      (motive := fun r : ℕ × ℕ =>
                        n ∈ Finset.Ico r.1 r.2)
                      hpkq.symm
                      hnq
                  have hn_bounds :
                      max pk.1.1 (right pk.2).1 ≤ n ∧
                        n < min pk.1.2 (right pk.2).2 :=
                    Finset.mem_Ico.mp hn_component
                  have hn_left_Ico : n ∈ Finset.Ico pk.1.1 pk.1.2 :=
                    Finset.mem_Ico.mpr
                      (And.intro
                        (le_trans (Nat.le_max_left pk.1.1 (right pk.2).1)
                          hn_bounds.1)
                        (lt_of_lt_of_le hn_bounds.2
                          (Nat.min_le_left pk.1.2 (right pk.2).2)))
                  have hn_right_Ico :
                      n ∈ Finset.Ico (right pk.2).1 (right pk.2).2 :=
                    Finset.mem_Ico.mpr
                      (And.intro
                        (le_trans (Nat.le_max_right pk.1.1 (right pk.2).1)
                          hn_bounds.1)
                        (lt_of_lt_of_le hn_bounds.2
                          (Nat.min_le_right pk.1.2 (right pk.2).2)))
                  have hn_left : n ∈ Complex.realPhase_IcoFamilyUnion left :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro pk.1 (And.intro hp_mem hn_left_Ico))
                  have hright_mem :
                      right pk.2 ∈ K.image right :=
                    Finset.mem_image.mpr
                      (Exists.intro pk.2 (And.intro hk_mem rfl))
                  have hn_right :
                      n ∈ Complex.realPhase_IcoFamilyUnion (K.image right) :=
                    Finset.mem_biUnion.mpr
                      (Exists.intro (right pk.2)
                        (And.intro hright_mem hn_right_Ico))
                  Finset.mem_filter.mpr (And.intro hn_left hn_right))
        (fun hn =>
          have hn_data :
              n ∈ Complex.realPhase_IcoFamilyUnion left ∧
                n ∈ Complex.realPhase_IcoFamilyUnion (K.image right) :=
            Finset.mem_filter.mp hn
          have hleft :
              ∃ p : ℕ × ℕ,
                p ∈ left ∧ n ∈ Finset.Ico p.1 p.2 :=
            Finset.mem_biUnion.mp hn_data.1
          have hright :
              ∃ r : ℕ × ℕ,
                r ∈ K.image right ∧ n ∈ Finset.Ico r.1 r.2 :=
            Finset.mem_biUnion.mp hn_data.2
          match hleft with
          | ⟨p, hp, hnp⟩ =>
              match hright with
              | ⟨r, hr, hnr⟩ =>
                  have hr_pre : ∃ k : ℤ, k ∈ K ∧ right k = r :=
                    Finset.mem_image.mp hr
                  match hr_pre with
                  | ⟨k, hk, hkr⟩ =>
                      have hn_right :
                          n ∈ Finset.Ico (right k).1 (right k).2 :=
                        Eq.subst
                          (motive := fun s : ℕ × ℕ =>
                            n ∈ Finset.Ico s.1 s.2)
                          hkr.symm
                          hnr
                      let q : ℕ × ℕ :=
                        (max p.1 (right k).1, min p.2 (right k).2)
                      have hnq : n ∈ Finset.Ico q.1 q.2 := by
                        have hp_bounds : p.1 ≤ n ∧ n < p.2 :=
                          Finset.mem_Ico.mp hnp
                        have hr_bounds :
                            (right k).1 ≤ n ∧ n < (right k).2 :=
                          Finset.mem_Ico.mp hn_right
                        have hleft_q : q.1 ≤ n :=
                          max_le hp_bounds.1 hr_bounds.1
                        have hright_q : n < q.2 :=
                          lt_min hp_bounds.2 hr_bounds.2
                        exact Finset.mem_Ico.mpr (And.intro hleft_q hright_q)
                      have hq_nonempty : q.1 < q.2 :=
                        (Finset.mem_Ico.mp hnq).2
                      have hq_image :
                          q ∈
                            Complex.realPhase_IcoFamily_pairwiseIntersections
                              left K right := by
                        exact
                          Finset.mem_image.mpr
                            (Exists.intro (p, k)
                              (And.intro
                                (Finset.mem_product.mpr (And.intro hp hk))
                                rfl))
                      have hq_refined :
                          q ∈
                            (Complex.realPhase_IcoFamily_pairwiseIntersections
                              left K right).filter
                              (fun q : ℕ × ℕ => q.1 < q.2) :=
                        Finset.mem_filter.mpr
                          (And.intro hq_image hq_nonempty)
                      Finset.mem_biUnion.mpr
                        (Exists.intro q (And.intro hq_refined hnq))))

/-- Pairwise-intersection components sharing a sample have the same left and
right witnesses. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_common_sample_witness_eq
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ∀ pk₁ : (ℕ × ℕ) × ℤ,
      pk₁ ∈ left.product K →
        ∀ pk₂ : (ℕ × ℕ) × ℤ,
          pk₂ ∈ left.product K →
            ∀ n : ℕ,
              n ∈
              (Finset.Ico
                (max pk₁.1.1 (right pk₁.2).1)
                (min pk₁.1.2 (right pk₁.2).2)) →
              n ∈
              (Finset.Ico
                (max pk₂.1.1 (right pk₂.2).1)
                (min pk₂.1.2 (right pk₂.2).2)) →
              pk₁.1 = pk₂.1 ∧ pk₁.2 = pk₂.2 := by
  intro pk₁ hpk₁ pk₂ hpk₂ n hn₁ hn₂
  have hpk₁_left : pk₁.1 ∈ left :=
    (Finset.mem_product.mp hpk₁).1
  have hpk₂_left : pk₂.1 ∈ left :=
    (Finset.mem_product.mp hpk₂).1
  have hpk₁_right : pk₁.2 ∈ K :=
    (Finset.mem_product.mp hpk₁).2
  have hpk₂_right : pk₂.2 ∈ K :=
    (Finset.mem_product.mp hpk₂).2
  have hn₁_bounds :
      max pk₁.1.1 (right pk₁.2).1 ≤ n ∧
        n < min pk₁.1.2 (right pk₁.2).2 :=
    Finset.mem_Ico.mp hn₁
  have hn₂_bounds :
      max pk₂.1.1 (right pk₂.2).1 ≤ n ∧
        n < min pk₂.1.2 (right pk₂.2).2 :=
    Finset.mem_Ico.mp hn₂
  have hn₁_left : n ∈ Finset.Ico pk₁.1.1 pk₁.1.2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (le_trans (Nat.le_max_left pk₁.1.1 (right pk₁.2).1)
          hn₁_bounds.1)
        (lt_of_lt_of_le hn₁_bounds.2
          (Nat.min_le_left pk₁.1.2 (right pk₁.2).2)))
  have hn₂_left : n ∈ Finset.Ico pk₂.1.1 pk₂.1.2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (le_trans (Nat.le_max_left pk₂.1.1 (right pk₂.2).1)
          hn₂_bounds.1)
        (lt_of_lt_of_le hn₂_bounds.2
          (Nat.min_le_left pk₂.1.2 (right pk₂.2).2)))
  have hn₁_right : n ∈ Finset.Ico (right pk₁.2).1 (right pk₁.2).2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (le_trans (Nat.le_max_right pk₁.1.1 (right pk₁.2).1)
          hn₁_bounds.1)
        (lt_of_lt_of_le hn₁_bounds.2
          (Nat.min_le_right pk₁.1.2 (right pk₁.2).2)))
  have hn₂_right : n ∈ Finset.Ico (right pk₂.2).1 (right pk₂.2).2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (le_trans (Nat.le_max_right pk₂.1.1 (right pk₂.2).1)
          hn₂_bounds.1)
        (lt_of_lt_of_le hn₂_bounds.2
          (Nat.min_le_right pk₂.1.2 (right pk₂.2).2)))
  have hleft_eq : pk₁.1 = pk₂.1 :=
    Classical.byContradiction
      (fun hne_left =>
        have hdis :
            Disjoint (Finset.Ico pk₁.1.1 pk₁.1.2)
              (Finset.Ico pk₂.1.1 pk₂.1.2) :=
          hleft_disjoint pk₁.1 hpk₁_left pk₂.1 hpk₂_left hne_left
        (Finset.disjoint_left.mp hdis) hn₁_left hn₂_left)
  have hright_eq : pk₁.2 = pk₂.2 :=
    Classical.byContradiction
      (fun hne_right =>
        have hdis :
            Disjoint (Finset.Ico (right pk₁.2).1 (right pk₁.2).2)
              (Finset.Ico (right pk₂.2).1 (right pk₂.2).2) :=
          hright_disjoint pk₁.2 hpk₁_right pk₂.2 hpk₂_right hne_right
        (Finset.disjoint_left.mp hdis) hn₁_right hn₂_right)
  exact And.intro hleft_eq hright_eq

/-- Pairwise intersections of two disjoint interval families are disjoint. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_disjoint
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ∀ q₁ : ℕ × ℕ,
      q₁ ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2) →
        ∀ q₂ : ℕ × ℕ,
          q₂ ∈
            (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
              (fun q : ℕ × ℕ => q.1 < q.2) →
            q₁ ≠ q₂ →
              Disjoint (Finset.Ico q₁.1 q₁.2) (Finset.Ico q₂.1 q₂.2) := by
  intro q₁ hq₁ q₂ hq₂ hne
  exact Finset.disjoint_left.mpr
    (fun n hn₁ hn₂ =>
      have hq₁_image :
          q₁ ∈ Complex.realPhase_IcoFamily_pairwiseIntersections left K right :=
        (Finset.mem_filter.mp hq₁).1
      have hq₂_image :
          q₂ ∈ Complex.realPhase_IcoFamily_pairwiseIntersections left K right :=
        (Finset.mem_filter.mp hq₂).1
      have hpre₁ :
          ∃ pk : (ℕ × ℕ) × ℤ,
            pk ∈ left.product K ∧
              (fun pk : (ℕ × ℕ) × ℤ =>
                (max pk.1.1 (right pk.2).1,
                  min pk.1.2 (right pk.2).2)) pk = q₁ :=
        Finset.mem_image.mp hq₁_image
      have hpre₂ :
          ∃ pk : (ℕ × ℕ) × ℤ,
            pk ∈ left.product K ∧
              (fun pk : (ℕ × ℕ) × ℤ =>
                (max pk.1.1 (right pk.2).1,
                  min pk.1.2 (right pk.2).2)) pk = q₂ :=
        Finset.mem_image.mp hq₂_image
      match hpre₁ with
      | ⟨pk₁, hpk₁, hpkq₁⟩ =>
          match hpre₂ with
          | ⟨pk₂, hpk₂, hpkq₂⟩ =>
              have hn₁_component :
                  n ∈ Finset.Ico
                    (max pk₁.1.1 (right pk₁.2).1)
                    (min pk₁.1.2 (right pk₁.2).2) :=
                Eq.subst
                  (motive := fun q : ℕ × ℕ =>
                    n ∈ Finset.Ico q.1 q.2)
                  hpkq₁.symm
                  hn₁
              have hn₂_component :
                  n ∈ Finset.Ico
                    (max pk₂.1.1 (right pk₂.2).1)
                    (min pk₂.1.2 (right pk₂.2).2) :=
                Eq.subst
                  (motive := fun q : ℕ × ℕ =>
                    n ∈ Finset.Ico q.1 q.2)
                  hpkq₂.symm
                  hn₂
              have hwitness :
                  pk₁.1 = pk₂.1 ∧ pk₁.2 = pk₂.2 :=
                Complex.realPhase_IcoFamily_pairwiseIntersections_common_sample_witness_eq
                  (a := a) (b := b)
                  left K right hleft_disjoint hright_disjoint
                  pk₁ hpk₁ pk₂ hpk₂ n hn₁_component hn₂_component
              have hpk_eq : pk₁ = pk₂ :=
                Prod.ext hwitness.1 hwitness.2
              have hq_eq : q₁ = q₂ :=
                Eq.trans hpkq₁.symm
                  (Eq.trans
                    (congrArg
                      (fun pk : (ℕ × ℕ) × ℤ =>
                        (max pk.1.1 (right pk.2).1,
                          min pk.1.2 (right pk.2).2))
                      hpk_eq)
                    hpkq₂)
              hne hq_eq)

/-- Pairwise intersections are bounded by the common ambient block. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_bounded
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b) :
    ∀ q : ℕ × ℕ,
      q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2) →
        a ≤ q.1 ∧ q.2 ≤ b := by
  intro q hq
  have hq_image :
      q ∈ Complex.realPhase_IcoFamily_pairwiseIntersections left K right :=
    (Finset.mem_filter.mp hq).1
  have hpre :
      ∃ pk : (ℕ × ℕ) × ℤ,
        pk ∈ left.product K ∧
          (fun pk : (ℕ × ℕ) × ℤ =>
            (max pk.1.1 (right pk.2).1,
              min pk.1.2 (right pk.2).2)) pk = q :=
    Finset.mem_image.mp hq_image
  match hpre with
  | ⟨pk, hpk, hpkq⟩ =>
      have hp_mem : pk.1 ∈ left :=
        (Finset.mem_product.mp hpk).1
      have hk_mem : pk.2 ∈ K :=
        (Finset.mem_product.mp hpk).2
      have hp_bounds : a ≤ pk.1.1 ∧ pk.1.2 ≤ b :=
        hleft_bounded pk.1 hp_mem
      have hk_bounds : a ≤ (right pk.2).1 ∧ (right pk.2).2 ≤ b :=
        hright_bounded pk.2 hk_mem
      have hcomponent_bounds :
          a ≤ (max pk.1.1 (right pk.2).1,
              min pk.1.2 (right pk.2).2).1 ∧
            (max pk.1.1 (right pk.2).1,
              min pk.1.2 (right pk.2).2).2 ≤ b := by
        have hleft_endpoint :
            a ≤ max pk.1.1 (right pk.2).1 :=
          le_trans hp_bounds.1 (Nat.le_max_left pk.1.1 (right pk.2).1)
        have hright_endpoint :
            min pk.1.2 (right pk.2).2 ≤ b :=
          le_trans (Nat.min_le_left pk.1.2 (right pk.2).2) hp_bounds.2
        exact And.intro hleft_endpoint hright_endpoint
      exact
        Eq.subst
          (motive := fun r : ℕ × ℕ => a ≤ r.1 ∧ r.2 ≤ b)
          hpkq
          hcomponent_bounds

/-- Every pairwise-intersection component remembers its parent left interval
and right center. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parent
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ) :
    ∀ q : ℕ × ℕ,
      q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2) →
        ∃ p : ℕ × ℕ,
          p ∈ left ∧
            ∃ k : ℤ,
              k ∈ K ∧
                Finset.Ico q.1 q.2 =
                  (Finset.Ico p.1 p.2).filter
                    (fun n : ℕ =>
                      n ∈ Finset.Ico (right k).1 (right k).2) ∧
                Finset.Ico q.1 q.2 ⊆
                  Finset.Ico (right k).1 (right k).2 := by
  intro q hq
  have hq_image :
      q ∈ Complex.realPhase_IcoFamily_pairwiseIntersections left K right :=
    (Finset.mem_filter.mp hq).1
  have hpre :
      ∃ pk : (ℕ × ℕ) × ℤ,
        pk ∈ left.product K ∧
          (fun pk : (ℕ × ℕ) × ℤ =>
            (max pk.1.1 (right pk.2).1,
              min pk.1.2 (right pk.2).2)) pk = q :=
    Finset.mem_image.mp hq_image
  match hpre with
  | ⟨pk, hpk, hpkq⟩ =>
      have hp_mem : pk.1 ∈ left :=
        (Finset.mem_product.mp hpk).1
      have hk_mem : pk.2 ∈ K :=
        (Finset.mem_product.mp hpk).2
      let component : ℕ × ℕ :=
        (max pk.1.1 (right pk.2).1, min pk.1.2 (right pk.2).2)
      have hcomponent_eq : component = q := by
        exact hpkq
      have hfilter_component :
          Finset.Ico component.1 component.2 =
            (Finset.Ico pk.1.1 pk.1.2).filter
              (fun n : ℕ =>
                n ∈ Finset.Ico (right pk.2).1 (right pk.2).2) := by
        exact
          (Nat.Ico_filter_mem_Ico_eq_Ico_max_min
            pk.1 (right pk.2)).symm
      have hsubset_component :
          Finset.Ico component.1 component.2 ⊆
            Finset.Ico (right pk.2).1 (right pk.2).2 := by
        intro n hn
        have hn_filter :
            n ∈ (Finset.Ico pk.1.1 pk.1.2).filter
              (fun n : ℕ =>
                n ∈ Finset.Ico (right pk.2).1 (right pk.2).2) :=
          Eq.subst
            (motive := fun S : Finset ℕ => n ∈ S)
            hfilter_component
            hn
        exact (Finset.mem_filter.mp hn_filter).2
      have hfilter_q :
          Finset.Ico q.1 q.2 =
            (Finset.Ico pk.1.1 pk.1.2).filter
              (fun n : ℕ =>
                n ∈ Finset.Ico (right pk.2).1 (right pk.2).2) :=
        Eq.subst
          (motive := fun r : ℕ × ℕ =>
            Finset.Ico r.1 r.2 =
              (Finset.Ico pk.1.1 pk.1.2).filter
                (fun n : ℕ =>
                  n ∈ Finset.Ico (right pk.2).1 (right pk.2).2))
          hcomponent_eq
          hfilter_component
      have hsubset_q :
          Finset.Ico q.1 q.2 ⊆
            Finset.Ico (right pk.2).1 (right pk.2).2 :=
        Eq.subst
          (motive := fun r : ℕ × ℕ =>
            Finset.Ico r.1 r.2 ⊆
              Finset.Ico (right pk.2).1 (right pk.2).2)
          hcomponent_eq
          hsubset_component
      exact
        Exists.intro pk.1
          (And.intro hp_mem
            (Exists.intro pk.2
              (And.intro hk_mem
                (And.intro hfilter_q hsubset_q))))

/-- Chosen parent data for a nonempty pairwise-intersection component. -/
def Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)}) :
    {p : ℕ × ℕ // p ∈ left} × {k : ℤ // k ∈ K} :=
  let hparent :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parent
      left K right q.1 q.2
  let p := Classical.choose hparent
  let hp := (Classical.choose_spec hparent).1
  let k := Classical.choose (Classical.choose_spec hparent).2
  let hk := (Classical.choose_spec (Classical.choose_spec hparent).2).1
  (⟨p, hp⟩, ⟨k, hk⟩)

/-- The chosen parent data reconstructs the component as the filtered
intersection of its chosen left interval with its chosen right interval. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_filter_eq
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)}) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    Finset.Ico q.1.1 q.1.2 =
      (Finset.Ico data.1.1.1 data.1.1.2).filter
        (fun n : ℕ =>
          n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) := by
  let hparent :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parent
      left K right q.1 q.2
  let p := Classical.choose hparent
  let hp := (Classical.choose_spec hparent).1
  let k := Classical.choose (Classical.choose_spec hparent).2
  let hk := (Classical.choose_spec (Classical.choose_spec hparent).2).1
  have hfilter :
      Finset.Ico q.1.1 q.1.2 =
        (Finset.Ico p.1 p.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right k).1 (right k).2) :=
    (Classical.choose_spec (Classical.choose_spec hparent).2).2.1
  exact hfilter

/-- The chosen component is contained in its chosen right parent interval. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_subset_right
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)}) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    Finset.Ico q.1.1 q.1.2 ⊆
      Finset.Ico (right data.2.1).1 (right data.2.1).2 := by
  let hparent :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parent
      left K right q.1 q.2
  let p := Classical.choose hparent
  let hp := (Classical.choose_spec hparent).1
  let k := Classical.choose (Classical.choose_spec hparent).2
  let hk := (Classical.choose_spec (Classical.choose_spec hparent).2).1
  have hsubset :
      Finset.Ico q.1.1 q.1.2 ⊆
        Finset.Ico (right k).1 (right k).2 :=
    (Classical.choose_spec (Classical.choose_spec hparent).2).2.2
  exact hsubset

/-- Membership in a component gives membership in its chosen left parent. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_left
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)})
    {n : ℕ}
    (hn : n ∈ Finset.Ico q.1.1 q.1.2) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    n ∈ Finset.Ico data.1.1.1 data.1.1.2 := by
  let data :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q
  have hfilter :
      Finset.Ico q.1.1 q.1.2 =
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_filter_eq
      left K right q
  have hn_filter :
      n ∈
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Eq.subst
      (motive := fun S : Finset ℕ => n ∈ S)
      hfilter
      hn
  exact (Finset.mem_filter.mp hn_filter).1

/-- Membership in a component gives membership in its chosen right parent. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_right
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)})
    {n : ℕ}
    (hn : n ∈ Finset.Ico q.1.1 q.1.2) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2 := by
  let data :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q
  have hsubset :
      Finset.Ico q.1.1 q.1.2 ⊆
        Finset.Ico (right data.2.1).1 (right data.2.1).2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_subset_right
      left K right q
  exact hsubset hn

/-- A nonempty filtered pairwise component contains its left endpoint. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_left_endpoint_mem
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)}) :
    q.1.1 ∈ Finset.Ico q.1.1 q.1.2 := by
  have hlt : q.1.1 < q.1.2 :=
    (Finset.mem_filter.mp q.2).2
  exact Finset.mem_Ico.mpr (And.intro (Nat.le_refl q.1.1) hlt)

/-- If the right parent starts no later than the left parent, then the left
parent start belongs to the chosen intersection component. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_leftStart_mem
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)})
    (hstart :
      let data :=
        Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
          left K right q
      (right data.2.1).1 ≤ data.1.1.1) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    data.1.1.1 ∈ Finset.Ico q.1.1 q.1.2 := by
  let data :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q
  have hnq :
      q.1.1 ∈ Finset.Ico q.1.1 q.1.2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_left_endpoint_mem
      left K right q
  have hn_left :
      q.1.1 ∈ Finset.Ico data.1.1.1 data.1.1.2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_left
      left K right q hnq
  have hn_right :
      q.1.1 ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_right
      left K right q hnq
  have hn_left_bounds :
      data.1.1.1 ≤ q.1.1 ∧ q.1.1 < data.1.1.2 :=
    Finset.mem_Ico.mp hn_left
  have hn_right_bounds :
      (right data.2.1).1 ≤ q.1.1 ∧ q.1.1 < (right data.2.1).2 :=
    Finset.mem_Ico.mp hn_right
  have hleft_start_left :
      data.1.1.1 ∈ Finset.Ico data.1.1.1 data.1.1.2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (Nat.le_refl data.1.1.1)
        (lt_of_le_of_lt hn_left_bounds.1 hn_left_bounds.2))
  have hleft_start_right :
      data.1.1.1 ∈
        Finset.Ico (right data.2.1).1 (right data.2.1).2 :=
    Finset.mem_Ico.mpr
      (And.intro
        hstart
        (lt_of_le_of_lt hn_left_bounds.1 hn_right_bounds.2))
  have hfilter :
      Finset.Ico q.1.1 q.1.2 =
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_filter_eq
      left K right q
  have hmem_filter :
      data.1.1.1 ∈
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Finset.mem_filter.mpr
      (And.intro hleft_start_left hleft_start_right)
  exact
    Eq.subst
      (motive := fun S : Finset ℕ => data.1.1.1 ∈ S)
      hfilter.symm
      hmem_filter

/-- If the right parent starts after the left parent, then the right parent
start belongs to the chosen intersection component. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_rightStart_mem
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)})
    (hstart :
      ¬
        (let data :=
          Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
            left K right q
        (right data.2.1).1 ≤ data.1.1.1)) :
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    (right data.2.1).1 ∈ Finset.Ico q.1.1 q.1.2 := by
  let data :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q
  have hnq :
      q.1.1 ∈ Finset.Ico q.1.1 q.1.2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_left_endpoint_mem
      left K right q
  have hn_left :
      q.1.1 ∈ Finset.Ico data.1.1.1 data.1.1.2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_left
      left K right q hnq
  have hn_right :
      q.1.1 ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_mem_right
      left K right q hnq
  have hn_left_bounds :
      data.1.1.1 ≤ q.1.1 ∧ q.1.1 < data.1.1.2 :=
    Finset.mem_Ico.mp hn_left
  have hn_right_bounds :
      (right data.2.1).1 ≤ q.1.1 ∧ q.1.1 < (right data.2.1).2 :=
    Finset.mem_Ico.mp hn_right
  have hleft_lt_right :
      data.1.1.1 < (right data.2.1).1 :=
    Nat.lt_of_not_ge hstart
  have hright_start_left :
      (right data.2.1).1 ∈ Finset.Ico data.1.1.1 data.1.1.2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (le_of_lt hleft_lt_right)
        (lt_of_le_of_lt hn_right_bounds.1 hn_left_bounds.2))
  have hright_start_right :
      (right data.2.1).1 ∈
        Finset.Ico (right data.2.1).1 (right data.2.1).2 :=
    Finset.mem_Ico.mpr
      (And.intro
        (Nat.le_refl (right data.2.1).1)
        (lt_of_le_of_lt hn_right_bounds.1 hn_right_bounds.2))
  have hfilter :
      Finset.Ico q.1.1 q.1.2 =
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_filter_eq
      left K right q
  have hmem_filter :
      (right data.2.1).1 ∈
        (Finset.Ico data.1.1.1 data.1.1.2).filter
          (fun n : ℕ =>
            n ∈ Finset.Ico (right data.2.1).1 (right data.2.1).2) :=
    Finset.mem_filter.mpr
      (And.intro hright_start_left hright_start_right)
  exact
    Eq.subst
      (motive := fun S : Finset ℕ => (right data.2.1).1 ∈ S)
      hfilter.symm
      hmem_filter

/-- Explicit sweep charge for a nonempty pairwise-intersection component.  The
component is charged to the interval whose left endpoint is the component left
endpoint. -/
def Complex.realPhase_IcoFamily_pairwiseIntersections_charge
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ) :
    {q // q ∈
      (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
        (fun q : ℕ × ℕ => q.1 < q.2)} →
      Sum {p // p ∈ left} {k // k ∈ K} :=
  fun q =>
    let data :=
      Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
        left K right q
    if (right data.2.1).1 ≤ data.1.1.1 then
      Sum.inl data.1
    else
      Sum.inr data.2

/-- Two components with the same endpoint-sweep charge share an integer
sample. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_same_charge_common_sample
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (q₁ q₂ :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)})
    (hcharge :
      Complex.realPhase_IcoFamily_pairwiseIntersections_charge left K right q₁ =
        Complex.realPhase_IcoFamily_pairwiseIntersections_charge left K right q₂) :
    ∃ n : ℕ,
      n ∈ Finset.Ico q₁.1.1 q₁.1.2 ∧
        n ∈ Finset.Ico q₂.1.1 q₂.1.2 := by
  let data₁ :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q₁
  let data₂ :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_parentData
      left K right q₂
  by_cases hstart₁ : (right data₁.2.1).1 ≤ data₁.1.1.1
  · have hcharge₁ :
        Complex.realPhase_IcoFamily_pairwiseIntersections_charge
            left K right q₁ =
          Sum.inl data₁.1 := by
      show
        (if (right data₁.2.1).1 ≤ data₁.1.1.1 then
            Sum.inl data₁.1
          else
            Sum.inr data₁.2) =
          Sum.inl data₁.1
      exact if_pos hstart₁
    by_cases hstart₂ : (right data₂.2.1).1 ≤ data₂.1.1.1
    · have hcharge₂ :
          Complex.realPhase_IcoFamily_pairwiseIntersections_charge
              left K right q₂ =
            Sum.inl data₂.1 := by
        show
          (if (right data₂.2.1).1 ≤ data₂.1.1.1 then
              Sum.inl data₂.1
            else
              Sum.inr data₂.2) =
            Sum.inl data₂.1
        exact if_pos hstart₂
      have hsum :
          Sum.inl data₁.1 = Sum.inl data₂.1 :=
        Eq.trans hcharge₁.symm (Eq.trans hcharge hcharge₂)
      have hparent_eq : data₁.1 = data₂.1 :=
        Sum.inl.inj hsum
      have hmem₁ :
          data₁.1.1.1 ∈ Finset.Ico q₁.1.1 q₁.1.2 :=
        Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_leftStart_mem
          left K right q₁ hstart₁
      have hmem₂_raw :
          data₂.1.1.1 ∈ Finset.Ico q₂.1.1 q₂.1.2 :=
        Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_leftStart_mem
          left K right q₂ hstart₂
      have hleft_eq : data₁.1.1.1 = data₂.1.1.1 :=
        congrArg (fun p : {p : ℕ × ℕ // p ∈ left} => p.1.1)
          hparent_eq
      have hmem₂ :
          data₁.1.1.1 ∈ Finset.Ico q₂.1.1 q₂.1.2 :=
        Eq.subst
          (motive := fun n : ℕ => n ∈ Finset.Ico q₂.1.1 q₂.1.2)
          hleft_eq.symm
          hmem₂_raw
      exact Exists.intro data₁.1.1.1 (And.intro hmem₁ hmem₂)
    · have hcharge₂ :
          Complex.realPhase_IcoFamily_pairwiseIntersections_charge
              left K right q₂ =
            Sum.inr data₂.2 := by
        show
          (if (right data₂.2.1).1 ≤ data₂.1.1.1 then
              Sum.inl data₂.1
            else
              Sum.inr data₂.2) =
            Sum.inr data₂.2
        exact if_neg hstart₂
      have hsum :
          Sum.inl data₁.1 = Sum.inr data₂.2 :=
        Eq.trans hcharge₁.symm (Eq.trans hcharge hcharge₂)
      cases hsum
  · have hcharge₁ :
        Complex.realPhase_IcoFamily_pairwiseIntersections_charge
            left K right q₁ =
          Sum.inr data₁.2 := by
      show
        (if (right data₁.2.1).1 ≤ data₁.1.1.1 then
            Sum.inl data₁.1
          else
            Sum.inr data₁.2) =
          Sum.inr data₁.2
      exact if_neg hstart₁
    by_cases hstart₂ : (right data₂.2.1).1 ≤ data₂.1.1.1
    · have hcharge₂ :
          Complex.realPhase_IcoFamily_pairwiseIntersections_charge
              left K right q₂ =
            Sum.inl data₂.1 := by
        show
          (if (right data₂.2.1).1 ≤ data₂.1.1.1 then
              Sum.inl data₂.1
            else
              Sum.inr data₂.2) =
            Sum.inl data₂.1
        exact if_pos hstart₂
      have hsum :
          Sum.inr data₁.2 = Sum.inl data₂.1 :=
        Eq.trans hcharge₁.symm (Eq.trans hcharge hcharge₂)
      cases hsum
    · have hcharge₂ :
          Complex.realPhase_IcoFamily_pairwiseIntersections_charge
              left K right q₂ =
            Sum.inr data₂.2 := by
        show
          (if (right data₂.2.1).1 ≤ data₂.1.1.1 then
              Sum.inl data₂.1
            else
              Sum.inr data₂.2) =
            Sum.inr data₂.2
        exact if_neg hstart₂
      have hsum :
          Sum.inr data₁.2 = Sum.inr data₂.2 :=
        Eq.trans hcharge₁.symm (Eq.trans hcharge hcharge₂)
      have hparent_eq : data₁.2 = data₂.2 :=
        Sum.inr.inj hsum
      have hmem₁ :
          (right data₁.2.1).1 ∈ Finset.Ico q₁.1.1 q₁.1.2 :=
        Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_rightStart_mem
          left K right q₁ hstart₁
      have hmem₂_raw :
          (right data₂.2.1).1 ∈ Finset.Ico q₂.1.1 q₂.1.2 :=
        Complex.realPhase_IcoFamily_pairwiseIntersections_parentData_rightStart_mem
          left K right q₂ hstart₂
      have hright_eq :
          (right data₁.2.1).1 = (right data₂.2.1).1 :=
        congrArg
          (fun k : {k : ℤ // k ∈ K} => (right k.1).1)
          hparent_eq
      have hmem₂ :
          (right data₁.2.1).1 ∈ Finset.Ico q₂.1.1 q₂.1.2 :=
        Eq.subst
          (motive := fun n : ℕ => n ∈ Finset.Ico q₂.1.1 q₂.1.2)
          hright_eq.symm
          hmem₂_raw
      exact Exists.intro (right data₁.2.1).1 (And.intro hmem₁ hmem₂)

/-- The explicit endpoint sweep charge is injective. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_charge_injective
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b)
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    Function.Injective
      (Complex.realPhase_IcoFamily_pairwiseIntersections_charge
        left K right) := by
  intro q₁ q₂ hcharge
  have hcommon :
      ∃ n : ℕ,
        n ∈ Finset.Ico q₁.1.1 q₁.1.2 ∧
          n ∈ Finset.Ico q₂.1.1 q₂.1.2 :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_same_charge_common_sample
      left K right q₁ q₂ hcharge
  match hcommon with
  | ⟨n, hn₁, hn₂⟩ =>
      have hval_eq : q₁.1 = q₂.1 :=
        Classical.byContradiction
          (fun hne =>
            have hdis :
                Disjoint (Finset.Ico q₁.1.1 q₁.1.2)
                  (Finset.Ico q₂.1.1 q₂.1.2) :=
              Complex.realPhase_IcoFamily_pairwiseIntersections_disjoint
                (a := a) (b := b)
                left K right hleft_disjoint hright_disjoint
                q₁.1 q₁.2 q₂.1 q₂.2 hne
            (Finset.disjoint_left.mp hdis) hn₁ hn₂)
      exact Subtype.ext hval_eq

/-- The sweep charging map for nonempty intersections of two disjoint interval
families is injective into the disjoint sum of left intervals and right
interval labels. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_has_additive_charge
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b)
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ∃ charge :
      {q // q ∈
        (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
          (fun q : ℕ × ℕ => q.1 < q.2)} →
        Sum {p // p ∈ left} {k // k ∈ K},
      Function.Injective charge := by
  exact
    Exists.intro
      (Complex.realPhase_IcoFamily_pairwiseIntersections_charge left K right)
      (Complex.realPhase_IcoFamily_pairwiseIntersections_charge_injective
        left K right hleft_bounded hleft_disjoint hright_bounded
        hright_disjoint)

/-- An injective charge of a finite subtype into the disjoint sum of two
finite subtypes gives the corresponding additive cardinal bound. -/
theorem Finset.card_le_add_of_injective_subtype_sum_charge
    {α β γ : Type}
    [DecidableEq α]
    [DecidableEq β]
    [DecidableEq γ]
    (A : Finset α)
    (B : Finset β)
    (C : Finset γ)
    (charge : {x // x ∈ A} → Sum {y // y ∈ B} {z // z ∈ C})
    (hinj : Function.Injective charge) :
    A.card ≤ B.card + C.card := by
  have hle :
      Fintype.card {x // x ∈ A} ≤
        Fintype.card (Sum {y // y ∈ B} {z // z ∈ C}) :=
    Fintype.card_le_of_injective charge hinj
  have hA :
      Fintype.card {x // x ∈ A} = A.card :=
    Fintype.card_coe A
  have hB :
      Fintype.card {y // y ∈ B} = B.card :=
    Fintype.card_coe B
  have hC :
      Fintype.card {z // z ∈ C} = C.card :=
    Fintype.card_coe C
  have hsum :
      Fintype.card (Sum {y // y ∈ B} {z // z ∈ C}) =
        Fintype.card {y // y ∈ B} + Fintype.card {z // z ∈ C} :=
    Fintype.card_sum
  have hright :
      Fintype.card (Sum {y // y ∈ B} {z // z ∈ C}) =
        B.card + C.card :=
    Eq.trans hsum (congrArg₂ Nat.add hB hC)
  exact
    Eq.subst
      (motive := fun left : ℕ => left ≤ B.card + C.card)
      hA
      (Eq.subst
        (motive := fun right : ℕ =>
          Fintype.card {x // x ∈ A} ≤ right)
        hright
        hle)

/-- Disjoint interval families have at most additively many nonempty
pairwise intersections. -/
theorem Complex.realPhase_IcoFamily_pairwiseIntersections_card_le_additive
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b)
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ((Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
      (fun q : ℕ × ℕ => q.1 < q.2)).card ≤ left.card + K.card := by
  have hcharge :
      ∃ charge :
        {q // q ∈
          (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
            (fun q : ℕ × ℕ => q.1 < q.2)} →
          Sum {p // p ∈ left} {k // k ∈ K},
        Function.Injective charge :=
    Complex.realPhase_IcoFamily_pairwiseIntersections_has_additive_charge
      left K right hleft_bounded hleft_disjoint hright_bounded
      hright_disjoint
  match hcharge with
  | ⟨charge, hinj⟩ =>
      exact
        Finset.card_le_add_of_injective_subtype_sum_charge
          ((Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
            (fun q : ℕ × ℕ => q.1 < q.2))
          left K charge hinj

/-- Additive size bound for the nonempty intersections of two ordered
half-open interval families.

This is the pure finite sweep lemma behind the all-integer resonance
decomposition.  The left family is an arbitrary disjoint bounded gap family;
the right family is ordered by integer centers.  Sweeping from left to right,
each new nonempty component starts either a new left interval or the next
right interval, so the number of components is bounded by the sum of the two
family sizes. -/
theorem Complex.realPhase_IcoFamily_orderedIntersectionComponents_card_le_add
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b)
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ∃ refined : Finset (ℕ × ℕ),
      refined.card ≤ left.card + K.card ∧
        Complex.realPhase_IcoFamilyUnion refined =
          (Complex.realPhase_IcoFamilyUnion left).filter
            (fun n : ℕ =>
              n ∈ Complex.realPhase_IcoFamilyUnion (K.image right)) ∧
        (∀ q₁ : ℕ × ℕ,
          q₁ ∈ refined →
            ∀ q₂ : ℕ × ℕ,
              q₂ ∈ refined →
                q₁ ≠ q₂ →
                  Disjoint (Finset.Ico q₁.1 q₁.2)
                    (Finset.Ico q₂.1 q₂.2)) ∧
        (∀ q : ℕ × ℕ,
          q ∈ refined →
            a ≤ q.1 ∧ q.2 ≤ b) ∧
        ∀ q : ℕ × ℕ,
          q ∈ refined →
            ∃ p : ℕ × ℕ,
              p ∈ left ∧
                ∃ k : ℤ,
                  k ∈ K ∧
                    Finset.Ico q.1 q.2 =
                      (Finset.Ico p.1 p.2).filter
                        (fun n : ℕ =>
                          n ∈ Finset.Ico (right k).1 (right k).2) ∧
                    Finset.Ico q.1 q.2 ⊆
                      Finset.Ico (right k).1 (right k).2 := by
  let refined : Finset (ℕ × ℕ) :=
    (Complex.realPhase_IcoFamily_pairwiseIntersections left K right).filter
      (fun q : ℕ × ℕ => q.1 < q.2)
  have hcard :
      refined.card ≤ left.card + K.card := by
    unfold refined
    exact
      Complex.realPhase_IcoFamily_pairwiseIntersections_card_le_additive
        left K right hleft_bounded hleft_disjoint hright_bounded
        hright_disjoint
  have hunion :
      Complex.realPhase_IcoFamilyUnion refined =
        (Complex.realPhase_IcoFamilyUnion left).filter
          (fun n : ℕ =>
            n ∈ Complex.realPhase_IcoFamilyUnion (K.image right)) := by
    unfold refined
    exact
      Complex.realPhase_IcoFamily_pairwiseIntersections_union_eq
        left K right
  have hdis :
      ∀ q₁ : ℕ × ℕ,
        q₁ ∈ refined →
          ∀ q₂ : ℕ × ℕ,
            q₂ ∈ refined →
              q₁ ≠ q₂ →
                Disjoint (Finset.Ico q₁.1 q₁.2)
                  (Finset.Ico q₂.1 q₂.2) := by
    unfold refined
    exact
      Complex.realPhase_IcoFamily_pairwiseIntersections_disjoint
        (a := a) (b := b)
        left K right hleft_disjoint hright_disjoint
  have hbounded :
      ∀ q : ℕ × ℕ,
        q ∈ refined →
          a ≤ q.1 ∧ q.2 ≤ b := by
    unfold refined
    exact
      Complex.realPhase_IcoFamily_pairwiseIntersections_bounded
        left K right hleft_bounded hright_bounded
  have hparent :
      ∀ q : ℕ × ℕ,
        q ∈ refined →
          ∃ p : ℕ × ℕ,
            p ∈ left ∧
              ∃ k : ℤ,
                k ∈ K ∧
                  Finset.Ico q.1 q.2 =
                    (Finset.Ico p.1 p.2).filter
                      (fun n : ℕ =>
                        n ∈ Finset.Ico (right k).1 (right k).2) ∧
                  Finset.Ico q.1 q.2 ⊆
                    Finset.Ico (right k).1 (right k).2 := by
    unfold refined
    exact
      Complex.realPhase_IcoFamily_pairwiseIntersections_parent
        left K right
  exact Exists.intro refined
    (And.intro hcard
      (And.intro hunion
        (And.intro hdis
          (And.intro hbounded hparent))))

/-- Generic additive intersection bound for a disjoint interval family refined
by a monotone ordered interval family. -/
theorem Complex.realPhase_IcoFamily_refinement_by_IcoFamily_card_le_additive
    {a b : ℕ}
    (left : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (right : ℤ → ℕ × ℕ)
    (hleft_bounded :
      ∀ p : ℕ × ℕ,
        p ∈ left →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hleft_disjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ left →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ left →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hright_bounded :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).2 ≤ b)
    (hright_disjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) :
    ∃ refined : Finset (ℕ × ℕ),
      refined.card ≤ left.card + K.card ∧
        Complex.realPhase_IcoFamilyUnion refined =
          (Complex.realPhase_IcoFamilyUnion left).filter
            (fun n : ℕ =>
              n ∈ Complex.realPhase_IcoFamilyUnion (K.image right)) ∧
        (∀ q₁ : ℕ × ℕ,
          q₁ ∈ refined →
            ∀ q₂ : ℕ × ℕ,
              q₂ ∈ refined →
                q₁ ≠ q₂ →
                  Disjoint (Finset.Ico q₁.1 q₁.2)
                    (Finset.Ico q₂.1 q₂.2)) ∧
        (∀ q : ℕ × ℕ,
          q ∈ refined →
            a ≤ q.1 ∧ q.2 ≤ b) ∧
        ∀ q : ℕ × ℕ,
          q ∈ refined →
            ∃ p : ℕ × ℕ,
              p ∈ left ∧
                ∃ k : ℤ,
                  k ∈ K ∧
                    Finset.Ico q.1 q.2 =
                      (Finset.Ico p.1 p.2).filter
                        (fun n : ℕ =>
                          n ∈ Finset.Ico (right k).1 (right k).2) ∧
                    Finset.Ico q.1 q.2 ⊆
                      Finset.Ico (right k).1 (right k).2 := by
  exact
    Complex.realPhase_IcoFamily_orderedIntersectionComponents_card_le_add
      left K right hleft_bounded hleft_disjoint hright_bounded
      hright_disjoint

/-- Principal strips have a finite half-open representative family ordered by
their integer centers. -/
theorem Complex.realPhase_principalStrip_IcoRepresentatives
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (K : Finset ℤ)
    (hab : a ≤ b)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ right : ℤ → ℕ × ℕ,
      (∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).1 ≤ (right k).2 ∧
            (right k).2 ≤ b ∧
            Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
              Finset.Ico (right k).1 (right k).2) ∧
      (∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2)) := by
  let right : ℤ → ℕ × ℕ :=
    fun k : ℤ =>
      let hdata :
          ∃ c d : ℕ,
            a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
              Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
                Finset.Ico c d :=
        Complex.realPhase_integerIncrementPrincipalStrip_exists
          φ k hab hinc_mono
      (Classical.choose hdata,
        Classical.choose (Classical.choose_spec hdata))
  have hright :
      ∀ k : ℤ,
        k ∈ K →
          a ≤ (right k).1 ∧ (right k).1 ≤ (right k).2 ∧
            (right k).2 ≤ b ∧
            Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
              Finset.Ico (right k).1 (right k).2 := by
    intro k _hk
    let hdata :
        ∃ c d : ℕ,
          a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
            Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
              Finset.Ico c d :=
      Complex.realPhase_integerIncrementPrincipalStrip_exists
        φ k hab hinc_mono
    have hspec :
        a ≤ Classical.choose hdata ∧
          Classical.choose hdata ≤
            Classical.choose (Classical.choose_spec hdata) ∧
          Classical.choose (Classical.choose_spec hdata) ≤ b ∧
          Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
            Finset.Ico (Classical.choose hdata)
              (Classical.choose (Classical.choose_spec hdata)) :=
      Classical.choose_spec (Classical.choose_spec hdata)
    have hright_eq :
        right k =
          (Classical.choose hdata,
            Classical.choose (Classical.choose_spec hdata)) := by
      rfl
    exact
      Eq.subst
        (motive := fun p : ℕ × ℕ =>
          a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b ∧
            Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
              Finset.Ico p.1 p.2)
        hright_eq.symm
        hspec
  have hdisjoint :
      ∀ k : ℤ,
        k ∈ K →
          ∀ l : ℤ,
            l ∈ K →
              k ≠ l →
                Disjoint (Finset.Ico (right k).1 (right k).2)
                  (Finset.Ico (right l).1 (right l).2) := by
    intro k hk l hl hkl
    have hk_eq :
        Complex.realPhase_integerIncrementPrincipalStrip φ a b k =
          Finset.Ico (right k).1 (right k).2 :=
      (hright k hk).2.2.2
    have hl_eq :
        Complex.realPhase_integerIncrementPrincipalStrip φ a b l =
          Finset.Ico (right l).1 (right l).2 :=
      (hright l hl).2.2.2
    have hstrip_disjoint :
        Disjoint
          (Complex.realPhase_integerIncrementPrincipalStrip φ a b k)
          (Complex.realPhase_integerIncrementPrincipalStrip φ a b l) :=
      Complex.realPhase_integerIncrementPrincipalStrip_disjoint_of_ne φ hkl
    exact
      Eq.subst
        (motive := fun S : Finset ℕ =>
          Disjoint S (Finset.Ico (right l).1 (right l).2))
        hk_eq
        (Eq.subst
          (motive := fun S : Finset ℕ =>
            Disjoint
              (Complex.realPhase_integerIncrementPrincipalStrip φ a b k) S)
          hl_eq
          hstrip_disjoint)
  exact Exists.intro right (And.intro hright hdisjoint)

/-- Refining a bounded disjoint interval family by the monotone
principal-strip partition costs additively in the number of original gaps and
the number of principal centers. -/
theorem Complex.realPhase_principalStrip_refinement_card_le_additive
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hab : a ≤ b)
    (gaps : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (hbounded :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ refined : Finset (ℕ × ℕ),
      refined.card ≤ gaps.card + K.card ∧
        Complex.realPhase_IcoFamilyUnion refined =
          (Complex.realPhase_IcoFamilyUnion gaps).filter
            (fun n : ℕ =>
              n ∈
                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                  φ a b K) ∧
        (∀ q₁ : ℕ × ℕ,
          q₁ ∈ refined →
            ∀ q₂ : ℕ × ℕ,
              q₂ ∈ refined →
                q₁ ≠ q₂ →
                  Disjoint (Finset.Ico q₁.1 q₁.2)
                    (Finset.Ico q₂.1 q₂.2)) ∧
        (∀ q : ℕ × ℕ,
          q ∈ refined →
            a ≤ q.1 ∧ q.2 ≤ b) ∧
        ∀ q : ℕ × ℕ,
          q ∈ refined →
            ∃ p : ℕ × ℕ,
              p ∈ gaps ∧
                ∃ k : ℤ,
                  k ∈ K ∧
                    Finset.Ico q.1 q.2 =
                      (Finset.Ico p.1 p.2).filter
                        (fun n : ℕ =>
                          n ∈
                            Complex.realPhase_integerIncrementPrincipalStrip
                              φ a b k) ∧
                  Finset.Ico q.1 q.2 ⊆
                    Complex.realPhase_integerIncrementPrincipalStrip
                      φ a b k := by
  match
    Complex.realPhase_principalStrip_IcoRepresentatives
      φ K hab hinc_mono with
  | ⟨right, hright, hright_disjoint⟩ =>
      have hright_bounded :
          ∀ k : ℤ,
            k ∈ K →
              a ≤ (right k).1 ∧ (right k).2 ≤ b := by
        intro k hk
        exact And.intro (hright k hk).1 (hright k hk).2.2.1
      match
        Complex.realPhase_IcoFamily_refinement_by_IcoFamily_card_le_additive
          gaps K right hbounded hdisjoint hright_bounded
          hright_disjoint with
      | ⟨refined, hrefined_card, hrefined_cover_Ico,
          hrefined_disjoint, hrefined_bounded, hrefined_cells⟩ =>
          have hright_union :
              Complex.realPhase_IcoFamilyUnion (K.image right) =
                Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                  φ a b K := by
            exact Finset.ext
              (fun n =>
                Iff.intro
                  (fun hn =>
                    have hn_data :
                        ∃ p : ℕ × ℕ,
                          p ∈ K.image right ∧ n ∈ Finset.Ico p.1 p.2 :=
                      Finset.mem_biUnion.mp hn
                    match hn_data with
                    | ⟨p, hp, hn_p⟩ =>
                        have hp_pre :
                            ∃ k : ℤ, k ∈ K ∧ right k = p :=
                          Finset.mem_image.mp hp
                        match hp_pre with
                        | ⟨k, hk, hkp⟩ =>
                            have hn_right :
                                n ∈ Finset.Ico (right k).1 (right k).2 :=
                              Eq.subst
                                (motive := fun q : ℕ × ℕ =>
                                  n ∈ Finset.Ico q.1 q.2)
                                hkp.symm
                                hn_p
                            have hn_strip :
                                n ∈
                                  Complex.realPhase_integerIncrementPrincipalStrip
                                    φ a b k :=
                              Eq.subst
                                (motive := fun S : Finset ℕ => n ∈ S)
                                (hright k hk).2.2.2.symm
                                hn_right
                            (Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
                              φ).mpr
                              (Exists.intro k (And.intro hk hn_strip)))
                  (fun hn =>
                    have hn_data :
                        ∃ k : ℤ,
                          k ∈ K ∧
                            n ∈
                              Complex.realPhase_integerIncrementPrincipalStrip
                                φ a b k :=
                      (Complex.mem_realPhase_integerIncrementPrincipalStripFamilyUnion_iff
                        φ).mp hn
                    match hn_data with
                    | ⟨k, hk, hn_strip⟩ =>
                        have hn_right :
                            n ∈ Finset.Ico (right k).1 (right k).2 :=
                          Eq.subst
                            (motive := fun S : Finset ℕ => n ∈ S)
                            (hright k hk).2.2.2
                            hn_strip
                        have hright_mem : right k ∈ K.image right :=
                          Finset.mem_image.mpr
                            (Exists.intro k (And.intro hk rfl))
                        Finset.mem_biUnion.mpr
                          (Exists.intro (right k)
                            (And.intro hright_mem hn_right))))
          have hrefined_cover :
              Complex.realPhase_IcoFamilyUnion refined =
                (Complex.realPhase_IcoFamilyUnion gaps).filter
                  (fun n : ℕ =>
                    n ∈
                      Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                        φ a b K) :=
            Eq.trans hrefined_cover_Ico
              (congrArg
                (fun S : Finset ℕ =>
                  (Complex.realPhase_IcoFamilyUnion gaps).filter
                    (fun n : ℕ => n ∈ S))
                hright_union)
          have hrefined_principal :
              ∀ q : ℕ × ℕ,
                q ∈ refined →
                  ∃ p : ℕ × ℕ,
                    p ∈ gaps ∧
                      ∃ k : ℤ,
                        k ∈ K ∧
                          Finset.Ico q.1 q.2 =
                            (Finset.Ico p.1 p.2).filter
                              (fun n : ℕ =>
                                n ∈
                                  Complex.realPhase_integerIncrementPrincipalStrip
                                    φ a b k) ∧
                          Finset.Ico q.1 q.2 ⊆
                            Complex.realPhase_integerIncrementPrincipalStrip
                              φ a b k := by
            intro q hq
            match hrefined_cells q hq with
            | ⟨p, hp, k, hk, hfilter, hsubset⟩ =>
                have hfilter_strip :
                    Finset.Ico q.1 q.2 =
                      (Finset.Ico p.1 p.2).filter
                        (fun n : ℕ =>
                          n ∈
                            Complex.realPhase_integerIncrementPrincipalStrip
                              φ a b k) := by
                  exact
                    Eq.trans hfilter
                      (congrArg
                        (fun S : Finset ℕ =>
                          (Finset.Ico p.1 p.2).filter
                            (fun n : ℕ => n ∈ S))
                        (hright k hk).2.2.2.symm)
                have hsubset_strip :
                    Finset.Ico q.1 q.2 ⊆
                      Complex.realPhase_integerIncrementPrincipalStrip
                        φ a b k := by
                  intro n hn
                  have hn_right :
                      n ∈ Finset.Ico (right k).1 (right k).2 :=
                    hsubset hn
                  exact
                    Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      (hright k hk).2.2.2.symm
                      hn_right
                exact Exists.intro p
                  (And.intro hp
                    (Exists.intro k
                      (And.intro hk
                        (And.intro hfilter_strip hsubset_strip))))
          exact Exists.intro refined
            (And.intro hrefined_card
              (And.intro hrefined_cover
                (And.intro hrefined_disjoint
                  (And.intro hrefined_bounded hrefined_principal))))

/-- A bounded disjoint interval family, refined by the monotone principal-strip
partition determined by a finite integer-center range, admits a principal
branch assignment with additive cardinal budget. -/
theorem Complex.realPhase_exists_additivePrincipalRefinement
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hab : a ≤ b)
    (gaps : Finset (ℕ × ℕ))
    (K : Finset ℤ)
    (hbounded :
      ∀ p : ℕ × ℕ,
        p ∈ gaps →
          a ≤ p.1 ∧ p.2 ≤ b)
    (hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ gaps →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ gaps →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2)
                  (Finset.Ico p₂.1 p₂.2))
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b) :
    ∃ refined : Finset (ℕ × ℕ),
      ∃ center : ℕ × ℕ → ℤ,
        refined.card ≤ gaps.card + K.card ∧
          Complex.realPhase_IcoFamilyUnion refined =
            (Complex.realPhase_IcoFamilyUnion gaps).filter
              (fun n : ℕ =>
                n ∈
                  Complex.realPhase_integerIncrementPrincipalStripFamilyUnion
                    φ a b K) ∧
          (∀ q₁ : ℕ × ℕ,
            q₁ ∈ refined →
              ∀ q₂ : ℕ × ℕ,
                q₂ ∈ refined →
                  q₁ ≠ q₂ →
                    Disjoint (Finset.Ico q₁.1 q₁.2)
                      (Finset.Ico q₂.1 q₂.2)) ∧
          (∀ q : ℕ × ℕ,
            q ∈ refined →
              a ≤ q.1 ∧ q.2 ≤ b) ∧
          ∀ q : ℕ × ℕ,
            q ∈ refined →
              ∀ n : ℕ,
                n ∈ Finset.Ico q.1 q.2 →
                  Complex.realPhase_integerIncrement
                      (Complex.realPhase_integerLatticeShift φ (center q))
                      n ∈
                    Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  match
    Complex.realPhase_principalStrip_refinement_card_le_additive
      φ hab gaps K hbounded hdisjoint hinc_mono with
  | ⟨refined, hrefined_card, hrefined_cover, hrefined_disjoint,
      hrefined_bounded, hrefined_principal⟩ =>
      let center : ℕ × ℕ → ℤ :=
        fun q : ℕ × ℕ =>
          if hq : q ∈ refined then
            Classical.choose
              (show ∃ k : ℤ,
                Finset.Ico q.1 q.2 ⊆
                  Complex.realPhase_integerIncrementPrincipalStrip φ a b k from
                match hrefined_principal q hq with
                | ⟨_p, _hp, k, _hk, _hfilter, hsubset⟩ =>
                    Exists.intro k hsubset)
          else
            0
      have hcenter :
          ∀ q : ℕ × ℕ,
            q ∈ refined →
              ∀ n : ℕ,
                n ∈ Finset.Ico q.1 q.2 →
                  Complex.realPhase_integerIncrement
                      (Complex.realPhase_integerLatticeShift φ (center q))
                      n ∈
                    Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
        intro q hq n hn
        have hcenter_spec :
            Finset.Ico q.1 q.2 ⊆
              Complex.realPhase_integerIncrementPrincipalStrip φ a b (center q) := by
          let principalExists : ∃ k : ℤ,
              Finset.Ico q.1 q.2 ⊆
                Complex.realPhase_integerIncrementPrincipalStrip φ a b k :=
            match hrefined_principal q hq with
            | ⟨_p, _hp, k, _hk, _hfilter, hsubset⟩ =>
                Exists.intro k hsubset
          have hcenter_eq :
              center q = Classical.choose principalExists := by
            unfold center
            exact dif_pos hq
          have hchosen :
              Finset.Ico q.1 q.2 ⊆
                Complex.realPhase_integerIncrementPrincipalStrip
                  φ a b (Classical.choose principalExists) :=
            Classical.choose_spec principalExists
          exact
            Eq.subst
              (motive := fun k : ℤ =>
                Finset.Ico q.1 q.2 ⊆
                  Complex.realPhase_integerIncrementPrincipalStrip φ a b k)
              hcenter_eq.symm
              hchosen
        exact
          Complex.realPhase_integerIncrementPrincipalStrip_principal
            φ (hcenter_spec hn)
      exact Exists.intro refined
        (Exists.intro center
          (And.intro hrefined_card
            (And.intro hrefined_cover
              (And.intro hrefined_disjoint
                (And.intro hrefined_bounded hcenter)))))

end

end LFunctions
end Boundary
