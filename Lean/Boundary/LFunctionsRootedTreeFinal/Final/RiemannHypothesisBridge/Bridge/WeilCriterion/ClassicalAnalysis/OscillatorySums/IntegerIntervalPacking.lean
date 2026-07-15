import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FiniteSumNorm

/-!
# Packing integers in short real intervals

This owner proves the elementary cardinality fact used by endpoint-frequency
arguments: a real interval of width strictly less than one contains at most one
integer.  The proof is explicit and works for an arbitrary finite set once all
of its integer casts are known to lie between the same endpoints.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Int.cast_add_one
    (m : ℤ) :
    ((m + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := by
  exact (Int.cast_add (R := ℝ) m 1).trans
    (congrArg (fun value : ℝ => (m : ℝ) + value) Int.cast_one)

theorem Int.cast_succ_le_of_lt
    {m n : ℤ} (hmn : m < n) :
    (m : ℝ) + 1 ≤ (n : ℝ) := by
  have hint : m + 1 ≤ n := Int.add_one_le_iff.mpr hmn
  have hcast : ((m + 1 : ℤ) : ℝ) ≤ (n : ℝ) :=
    Int.cast_le.mpr hint
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ (n : ℝ))
    (Int.cast_add_one m)
    hcast

theorem Real.left_add_one_le_right_of_two_integer_points
    {left right : ℝ} {m n : ℤ}
    (hmLeft : left ≤ (m : ℝ))
    (hnRight : (n : ℝ) ≤ right)
    (hmn : m < n) :
    left + 1 ≤ right := by
  have hsucc := Int.cast_succ_le_of_lt hmn
  have hleftSucc := add_le_add_right hmLeft 1
  exact le_trans hleftSucc (le_trans hsucc hnRight)

theorem Real.not_left_add_one_le_right_of_width_lt_one
    {left right : ℝ}
    (hwidth : right - left < 1) :
    ¬ left + 1 ≤ right := by
  intro hle
  have hsub : (1 : ℝ) ≤ right - left := by
    exact (le_sub_iff_add_le).mpr
      (Eq.subst (motive := fun value : ℝ => value ≤ right)
        (add_comm left 1) hle)
  exact (not_le_of_gt hwidth) hsub

theorem Int.eq_of_cast_mem_short_interval
    {left right : ℝ} {m n : ℤ}
    (hwidth : right - left < 1)
    (hm : left ≤ (m : ℝ) ∧ (m : ℝ) ≤ right)
    (hn : left ≤ (n : ℝ) ∧ (n : ℝ) ≤ right) :
    m = n := by
  have hnotSpread :=
    Real.not_left_add_one_le_right_of_width_lt_one hwidth
  have hnotMN : ¬ m < n := by
    intro hmn
    exact hnotSpread
      (Real.left_add_one_le_right_of_two_integer_points
        hm.1 hn.2 hmn)
  have hnotNM : ¬ n < m := by
    intro hnm
    exact hnotSpread
      (Real.left_add_one_le_right_of_two_integer_points
        hn.1 hm.2 hnm)
  exact le_antisymm (le_of_not_gt hnotNM) (le_of_not_gt hnotMN)

theorem Finset.subset_singleton_of_cast_mem_short_interval
    (modes : Finset ℤ)
    {left right : ℝ}
    (hwidth : right - left < 1)
    (hmem : ∀ m ∈ modes,
      left ≤ (m : ℝ) ∧ (m : ℝ) ≤ right)
    {anchor : ℤ} (hanchor : anchor ∈ modes) :
    modes ⊆ {anchor} := by
  intro m hm
  have heq :=
    Int.eq_of_cast_mem_short_interval hwidth
      (hmem m hm) (hmem anchor hanchor)
  exact Finset.mem_singleton.mpr heq

theorem Finset.card_le_one_of_cast_mem_short_interval
    (modes : Finset ℤ)
    {left right : ℝ}
    (hwidth : right - left < 1)
    (hmem : ∀ m ∈ modes,
      left ≤ (m : ℝ) ∧ (m : ℝ) ≤ right) :
    modes.card ≤ 1 := by
  match modes.eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hcard : modes.card = 0 := by
        exact congrArg Finset.card hempty |>.trans Finset.card_empty
      exact Eq.subst
        (motive := fun value : ℕ => value ≤ 1)
        hcard.symm (Nat.zero_le 1)
  | Or.inr hnonempty =>
      let anchor : ℤ := hnonempty.choose
      have hanchor : anchor ∈ modes := hnonempty.choose_spec
      have hsubset : modes ⊆ {anchor} :=
        Finset.subset_singleton_of_cast_mem_short_interval
          modes hwidth hmem hanchor
      have hcardSubset := Finset.card_le_card hsubset
      have hsingleton : ({anchor} : Finset ℤ).card = 1 :=
        Finset.card_singleton anchor
      exact Eq.subst
        (motive := fun value : ℕ => modes.card ≤ value)
        hsingleton hcardSubset

theorem Finset.card_eq_zero_or_one_of_cast_mem_short_interval
    (modes : Finset ℤ)
    {left right : ℝ}
    (hwidth : right - left < 1)
    (hmem : ∀ m ∈ modes,
      left ≤ (m : ℝ) ∧ (m : ℝ) ≤ right) :
    modes.card = 0 ∨ modes.card = 1 := by
  have hcard :=
    Finset.card_le_one_of_cast_mem_short_interval
      modes hwidth hmem
  match Nat.eq_zero_or_pos modes.card with
  | Or.inl hzero => exact Or.inl hzero
  | Or.inr hpos =>
      have honeLe : 1 ≤ modes.card := hpos
      exact Or.inr (Nat.le_antisymm hcard honeLe)

/-- Translation of a short interval preserves its width. -/
theorem Real.translated_interval_width
    (left right shift : ℝ) :
    (right + shift) - (left + shift) = right - left := by
  calc
    (right + shift) - (left + shift) =
        right + shift + (-(left + shift)) :=
      sub_eq_add_neg _ _
    _ = right + shift + (-left + -shift) := by
      exact congrArg (fun value : ℝ => right + shift + value)
        (neg_add left shift)
    _ = right + (shift + (-left + -shift)) :=
      add_assoc right shift (-left + -shift)
    _ = right + ((shift + -shift) + -left) := by
      exact congrArg (fun value : ℝ => right + value)
        (calc
          shift + (-left + -shift) = (shift + -left) + -shift :=
            (add_assoc shift (-left) (-shift)).symm
          _ = (-left + shift) + -shift := by
            exact congrArg (fun value : ℝ => value + -shift)
              (add_comm shift (-left))
          _ = -left + (shift + -shift) :=
            add_assoc (-left) shift (-shift)
          _ = (shift + -shift) + -left :=
            add_comm (-left) (shift + -shift))
    _ = right + (0 + -left) := by
      exact congrArg (fun value : ℝ => right + (value + -left))
        (add_neg_cancel shift)
    _ = right + -left := by
      exact congrArg (fun value : ℝ => right + value) (zero_add (-left))
    _ = right - left := (sub_eq_add_neg right left).symm

end

end LFunctions
end Boundary
