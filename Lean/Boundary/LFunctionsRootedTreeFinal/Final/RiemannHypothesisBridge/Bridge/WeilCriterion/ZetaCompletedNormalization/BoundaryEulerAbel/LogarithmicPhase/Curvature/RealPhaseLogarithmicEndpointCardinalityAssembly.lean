import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointCardinality

/-!
# Assembly of endpoint-mode cardinality

The balanced endpoint family is covered by four geometrically meaningful
classes.  Each class has already been packed into a reflected frequency
interval of width less than one.  This file performs the finite-set assembly
without assuming that the classes are disjoint: repeated endpoint modes can
only decrease the cardinality of their union.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Finset.card_union_le_add_card_left
    {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).card ≤ s₁.card + s₂.card := by
  exact Finset.card_union_le s₁ s₂

theorem Finset.card_fourfold_union_le_sum
    {α : Type*} [DecidableEq α]
    (s₁ s₂ s₃ s₄ : Finset α) :
    (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤
      s₁.card + s₂.card + s₃.card + s₄.card := by
  have h₁₂ :
      (s₁ ∪ s₂).card ≤ s₁.card + s₂.card :=
    Finset.card_union_le_add_card_left s₁ s₂
  have h₁₂₃ :
      (s₁ ∪ s₂ ∪ s₃).card ≤ (s₁ ∪ s₂).card + s₃.card :=
    Finset.card_union_le_add_card_left (s₁ ∪ s₂) s₃
  have h₁₂₃₄ :
      (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤
        (s₁ ∪ s₂ ∪ s₃).card + s₄.card :=
    Finset.card_union_le_add_card_left (s₁ ∪ s₂ ∪ s₃) s₄
  have h₁₂₃_right :
      (s₁ ∪ s₂).card + s₃.card ≤
        (s₁.card + s₂.card) + s₃.card :=
    Nat.add_le_add_right h₁₂ s₃.card
  have h₁₂₃_bound :
      (s₁ ∪ s₂ ∪ s₃).card ≤
        (s₁.card + s₂.card) + s₃.card :=
    le_trans h₁₂₃ h₁₂₃_right
  have h₁₂₃₄_right :
      (s₁ ∪ s₂ ∪ s₃).card + s₄.card ≤
        ((s₁.card + s₂.card) + s₃.card) + s₄.card :=
    Nat.add_le_add_right h₁₂₃_bound s₄.card
  have hbound :
      (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤
        ((s₁.card + s₂.card) + s₃.card) + s₄.card :=
    le_trans h₁₂₃₄ h₁₂₃₄_right
  exact hbound

theorem Finset.card_fourfold_union_le_four
    {α : Type*} [DecidableEq α]
    (s₁ s₂ s₃ s₄ : Finset α)
    (h₁ : s₁.card ≤ 1)
    (h₂ : s₂.card ≤ 1)
    (h₃ : s₃.card ≤ 1)
    (h₄ : s₄.card ≤ 1) :
    (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤ 4 := by
  have h₁₂ : s₁.card + s₂.card ≤ 1 + 1 :=
    Nat.add_le_add h₁ h₂
  have h₁₂₃ :
      (s₁.card + s₂.card) + s₃.card ≤ (1 + 1) + 1 :=
    Nat.add_le_add h₁₂ h₃
  have h₁₂₃₄ :
      ((s₁.card + s₂.card) + s₃.card) + s₄.card ≤
        ((1 + 1) + 1) + 1 :=
    Nat.add_le_add h₁₂₃ h₄
  have hunion := Finset.card_fourfold_union_le_sum s₁ s₂ s₃ s₄
  have hcombined :
      (s₁ ∪ s₂ ∪ s₃ ∪ s₄).card ≤ ((1 + 1) + 1) + 1 :=
    le_trans hunion h₁₂₃₄
  exact hcombined

theorem Complex.logarithmicPhasePoissonBProcessEndpointPartitionUnion_card_le_four
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessLeftOutsideModes
        t (a : ℤ) (b : ℤ) ∪
      Complex.logarithmicPhasePoissonBProcessRightOutsideModes
        t (a : ℤ) (b : ℤ) ∪
      Complex.logarithmicPhasePoissonBProcessLeftClippedModes
        t (a : ℤ) (b : ℤ) ∪
      Complex.logarithmicPhasePoissonBProcessRightClippedModes
        t (a : ℤ) (b : ℤ)).card ≤ 4 := by
  have hleftOutside :=
    Complex.leftOutsideModes_card_le_one ht hgeometry
  have hrightOutside :=
    Complex.rightOutsideModes_card_le_one ht hgeometry
  have hleftClipped :=
    Complex.leftClippedModes_card_le_one ht hgeometry
  have hrightClipped :=
    Complex.rightClippedModes_card_le_one ht hgeometry
  exact Finset.card_fourfold_union_le_four
    (Complex.logarithmicPhasePoissonBProcessLeftOutsideModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessRightOutsideModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessLeftClippedModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessRightClippedModes
      t (a : ℤ) (b : ℤ))
    hleftOutside hrightOutside hleftClipped hrightClipped

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_partitionUnion
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b).card ≤
      (Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessLeftClippedModes t a b ∪
        Complex.logarithmicPhasePoissonBProcessRightClippedModes t a b).card := by
  exact Finset.card_le_card
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_partitionUnion
      t a b)

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_four
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)).card ≤ 4 := by
  have hsubsetCard :=
    Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_partitionUnion
      t (a : ℤ) (b : ℤ)
  have hunionCard :=
    Complex.logarithmicPhasePoissonBProcessEndpointPartitionUnion_card_le_four
      ht hgeometry
  exact le_trans hsubsetCard hunionCard

theorem Complex.logarithmicPhasePoissonBProcessEndpointModes_card_cast_le_four
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ((Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)).card : ℝ) ≤ 4 := by
  exact Nat.cast_le.mpr
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_four
      ht hgeometry)

theorem Finset.sum_le_card_mul_of_pointwise_le
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (C : ℝ)
    (hpoint : ∀ x ∈ s, f x ≤ C) :
    ∑ x ∈ s, f x ≤ (s.card : ℝ) * C := by
  have hsum :
      ∑ x ∈ s, f x ≤ ∑ x ∈ s, C :=
    Finset.sum_le_sum (fun x hx => hpoint x hx)
  have hconstant :
      ∑ x ∈ s, C = (s.card : ℝ) * C := by
    exact (Finset.sum_const C).trans
      (nsmul_eq_mul (s.card) C)
  exact hsum.trans_eq hconstant

theorem Finset.sum_le_four_mul_of_card_le_four
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (C : ℝ)
    (hcard : s.card ≤ 4)
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, f x ≤ C) :
    ∑ x ∈ s, f x ≤ 4 * C := by
  have hsum := Finset.sum_le_card_mul_of_pointwise_le s f C hpoint
  have hcast : (s.card : ℝ) ≤ 4 := Nat.cast_le.mpr hcard
  have hmul : (s.card : ℝ) * C ≤ 4 * C :=
    mul_le_mul_of_nonneg_right hcast hC
  exact le_trans hsum hmul

theorem Complex.logarithmicPhaseBProcessEndpointBudget_le_four_mul
    {t : ℝ} {a b : ℕ} (C : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hC : 0 ≤ C)
    (hpoint :
      ∀ m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
          t (a : ℤ) (b : ℤ),
        Complex.logarithmicPhaseBProcessEndpointPacketBudget
          t (a : ℤ) (b : ℤ) m ≤ C) :
    Complex.logarithmicPhaseBProcessEndpointBudget
        t (a : ℤ) (b : ℤ) ≤ 4 * C := by
  unfold Complex.logarithmicPhaseBProcessEndpointBudget
  exact Finset.sum_le_four_mul_of_card_le_four
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessEndpointPacketBudget
      t (a : ℤ) (b : ℤ))
    C
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_four
      ht hgeometry)
    hC hpoint

end

end LFunctions
end Boundary
