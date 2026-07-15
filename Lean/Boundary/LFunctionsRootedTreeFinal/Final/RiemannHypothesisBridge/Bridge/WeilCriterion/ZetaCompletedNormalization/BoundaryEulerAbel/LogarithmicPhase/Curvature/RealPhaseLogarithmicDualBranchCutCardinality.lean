import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualPrincipalRuns

/-!
# Cardinality of midpoint branch-cut cells

The continuous increment is strictly increasing, hence a fixed midpoint level
has at most one real preimage.  A real point belongs to at most two closed unit
cells.  Therefore each branch-cut level deletes at most two natural indices,
and the full branch-cut family has cardinality at most twice the number of
represented midpoint levels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes
    (t : ℝ) (h K M q : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ => Complex.logarithmicPhaseDualBranchCutCell t h n q)

theorem Complex.mem_logarithmicPhaseDualDiscreteLevelBranchCutModes_iff
    (t : ℝ) (h K M q n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes t h K M q ↔
      n ∈ Finset.Icc K M ∧
        Complex.logarithmicPhaseDualBranchCutCell t h n q := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhaseDualDiscreteBranchCutModes_eq_biUnion
    (t : ℝ) (h K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M =
      (Complex.logarithmicPhaseDualBranchCutLevels
        t (h : ℝ) (K : ℝ)).biUnion
        (fun q : ℕ =>
          Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes
            t h K M q) := by
  exact Finset.Subset.antisymm
    (fun n hn =>
      have hnMembership :=
        (Complex.mem_logarithmicPhaseDualDiscreteBranchCutModes_iff
          t h K M n).mp hn
      rcases hnMembership.2 with ⟨q, hq, hnCut⟩
      exact Finset.mem_biUnion.mpr
        (Exists.intro q
          (And.intro hq
            ((Complex.mem_logarithmicPhaseDualDiscreteLevelBranchCutModes_iff
              t h K M q n).mpr
              (And.intro hnMembership.1 hnCut))))
    (fun n hn =>
      rcases Finset.mem_biUnion.mp hn with ⟨q, hq, hnLevel⟩
      have hnMembership :=
        (Complex.mem_logarithmicPhaseDualDiscreteLevelBranchCutModes_iff
          t h K M q n).mp hnLevel
      exact
        (Complex.mem_logarithmicPhaseDualDiscreteBranchCutModes_iff
          t h K M n).mpr
          (And.intro hnMembership.1
            (Exists.intro q (And.intro hq hnMembership.2))))

theorem Complex.logarithmicPhaseDualBranchCutCell_crossing_unique
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h n m q : ℕ} (hh : 0 < h) (hn : 0 < n) (hm : 0 < m)
    (hnCut : Complex.logarithmicPhaseDualBranchCutCell t h n q)
    (hmCut : Complex.logarithmicPhaseDualBranchCutCell t h m q) :
    ∃ x : ℝ,
      x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∧
      x ∈ Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ) ∧
      |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x| =
        Complex.logarithmicPhaseDualBranchCutLevel q := by
  rcases hnCut with ⟨x, hx, hxLevel⟩
  rcases hmCut with ⟨y, hy, hyLevel⟩
  have hxPos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) hx.1
  have hyPos := lt_of_lt_of_le (Nat.cast_pos.mpr hm) hy.1
  have hxNeg :=
    Complex.logarithmicPhaseDualContinuousIncrement_neg
      t ht (Nat.cast_pos.mpr hh) hxPos
  have hyNeg :=
    Complex.logarithmicPhaseDualContinuousIncrement_neg
      t ht (Nat.cast_pos.mpr hh) hyPos
  have hxAbs := abs_of_neg hxNeg
  have hyAbs := abs_of_neg hyNeg
  have hvalues :
      Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x =
        Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) y := by
    have hnegValues :
        -Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x =
          -Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) y :=
      Eq.trans hxAbs.symm (Eq.trans hxLevel (Eq.trans hyLevel.symm hyAbs))
    exact neg_injective hnegValues
  have hxy : x = y := by
    match lt_trichotomy x y with
    | Or.inl hlt =>
        have hstrict :=
          Complex.logarithmicPhaseDualContinuousIncrement_strictMonoOn
            t ht (Nat.cast_pos.mpr hh) hxPos hyPos hlt
        exact False.elim (ne_of_lt hstrict hvalues)
    | Or.inr hrest =>
        match hrest with
        | Or.inl heq => exact heq
        | Or.inr hgt =>
            have hstrict :=
              Complex.logarithmicPhaseDualContinuousIncrement_strictMonoOn
                t ht (Nat.cast_pos.mpr hh) hyPos hxPos hgt
            exact False.elim (ne_of_lt hstrict hvalues.symm)
  exact Exists.intro x
    (And.intro hx
      (And.intro
        (Eq.subst (motive := fun z : ℝ => z ∈ Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ))
          hxy.symm hy)
        hxLevel))

theorem Nat.indices_of_cells_sharing_point_distance_le_one
    {n m : ℕ} {x : ℝ}
    (hn : x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ))
    (hm : x ∈ Set.Icc (m : ℝ) ((m + 1 : ℕ) : ℝ)) :
    |(n : ℝ) - (m : ℝ)| ≤ 1 := by
  match le_total n m with
  | Or.inl hnm =>
      have hmLeSuccN : m ≤ n + 1 := by
        exact Nat.cast_le.mp (le_trans hm.1 hn.2)
      have hsub : (m : ℝ) - (n : ℝ) ≤ 1 := by
        exact sub_le_iff_le_add.mpr
          (Eq.subst (motive := fun z : ℝ => (m : ℝ) ≤ z)
            (Nat.cast_add n 1).symm (Nat.cast_le.mpr hmLeSuccN))
      exact Eq.subst (motive := fun z : ℝ => z ≤ 1)
        (abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hnm))).symm
        (Eq.subst (motive := fun z : ℝ => z ≤ 1)
          (neg_sub (n : ℝ) (m : ℝ)).symm hsub)
  | Or.inr hmn =>
      have hnLeSuccM : n ≤ m + 1 :=
        Nat.cast_le.mp (le_trans hn.1 hm.2)
      have hsub : (n : ℝ) - (m : ℝ) ≤ 1 := by
        exact sub_le_iff_le_add.mpr
          (Eq.subst (motive := fun z : ℝ => (n : ℝ) ≤ z)
            (Nat.cast_add m 1).symm (Nat.cast_le.mpr hnLeSuccM))
      exact Eq.subst (motive := fun z : ℝ => z ≤ 1)
        (abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hmn))).symm hsub

theorem Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes_card_le_two
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M q : ℕ} (hh : 0 < h) (hK : 0 < K) :
    (Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes
      t h K M q).card ≤ 2 := by
  let S := Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes t h K M q
  have hdiameter : ∀ n ∈ S, ∀ m ∈ S,
      |(n : ℝ) - (m : ℝ)| ≤ (1 : ℝ) := by
    intro n hn m hm
    have hnMembership :=
      (Complex.mem_logarithmicPhaseDualDiscreteLevelBranchCutModes_iff
        t h K M q n).mp hn
    have hmMembership :=
      (Complex.mem_logarithmicPhaseDualDiscreteLevelBranchCutModes_iff
        t h K M q m).mp hm
    have hnPos := lt_of_lt_of_le hK (Finset.mem_Icc.mp hnMembership.1).1
    have hmPos := lt_of_lt_of_le hK (Finset.mem_Icc.mp hmMembership.1).1
    rcases Complex.logarithmicPhaseDualBranchCutCell_crossing_unique
      t ht hh hnPos hmPos hnMembership.2 hmMembership.2 with
      ⟨x, hxN, hxM, hxLevel⟩
    exact Nat.indices_of_cells_sharing_point_distance_le_one hxN hxM
  have hcardReal := Finset.card_real_le_diameter_add_one S 1 zero_le_one hdiameter
  have htwo : (1 : ℝ) + 1 = 2 := by exact rfl
  have hcardRealTwo : (S.card : ℝ) ≤ 2 :=
    Eq.subst (motive := fun z : ℝ => (S.card : ℝ) ≤ z) htwo.symm hcardReal
  exact Nat.cast_le.mp hcardRealTwo

theorem Complex.logarithmicPhaseDualDiscreteBranchCutModes_card_le_two_mul_levels
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) :
    (Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M).card ≤
      2 * (Complex.logarithmicPhaseDualBranchCutLevels
        t (h : ℝ) (K : ℝ)).card := by
  have heq :=
    Complex.logarithmicPhaseDualDiscreteBranchCutModes_eq_biUnion t h K M
  have hunion := Finset.card_biUnion_le_sum_card
    (Complex.logarithmicPhaseDualBranchCutLevels t (h : ℝ) (K : ℝ))
    (fun q : ℕ =>
      Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes t h K M q)
  have hpoint :
      (∑ q ∈ Complex.logarithmicPhaseDualBranchCutLevels
          t (h : ℝ) (K : ℝ),
        (Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes
          t h K M q).card) ≤
      ∑ q ∈ Complex.logarithmicPhaseDualBranchCutLevels
          t (h : ℝ) (K : ℝ), 2 := by
    exact Finset.sum_le_sum (fun q hq =>
      Complex.logarithmicPhaseDualDiscreteLevelBranchCutModes_card_le_two
        t ht hh hK)
  have hconstant := Finset.sum_const_zero
    (Complex.logarithmicPhaseDualBranchCutLevels t (h : ℝ) (K : ℝ)) 2
  exact Eq.subst (motive := fun S : Finset ℕ => S.card ≤ _)
    heq.symm
    (le_trans hunion (le_trans hpoint (le_of_eq hconstant)))

end

end LFunctions
end Boundary
