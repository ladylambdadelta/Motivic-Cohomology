import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectTails

/-!
# Inverse-square far Poisson tail

Schwartz decay supplies an inverse-square estimate only off a finite exceptional
set.  This file isolates that cofinite tail as its own owner object.  The
finite exceptional modes remain a separate finite contribution; no transition
estimate is silently summed over infinitely many frequencies.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonFarTailSet
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) : Set ℤ :=
  {m : ℤ |
    m ∉ Complex.logarithmicPhasePoissonModeRange t a ∧ m ∉ exceptional}

def Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) : Set ℤ :=
  {m : ℤ |
    m ∉ Complex.logarithmicPhasePoissonModeRange t a ∧ m ∈ exceptional}

def Complex.logarithmicPhasePoissonFarTailMajorant
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) (C : ℝ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonFarTailSet t a exceptional,
    C * |(m : ℝ)| ^ (-2 : ℝ)

def Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget
    (t : ℝ) (a b : ℤ) (exceptional : Set ℤ)
    (hfinite :
      (Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
        t a exceptional).Finite) : ℝ :=
  ∑ m ∈ hfinite.toFinset,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

theorem Complex.summable_logarithmicPhasePoissonFarTailMajorant
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) (C : ℝ) :
    Summable
      (fun m : Complex.logarithmicPhasePoissonFarTailSet t a exceptional =>
        C * |(m : ℝ)| ^ (-2 : ℝ)) := by
  exact
    Complex.summable_scaled_integer_frequency_inverse_square_on_set
      C (Complex.logarithmicPhasePoissonFarTailSet t a exceptional)

theorem Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet_finite
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ)
    (hexceptional : exceptional.Finite) :
    (Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
      t a exceptional).Finite := by
  exact
    Set.Finite.subset hexceptional
      (fun m hm => hm.2)

theorem Complex.logarithmicPhasePoissonFarTailSet_disjoint_exceptional
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonFarTailSet t a exceptional)
      exceptional := by
  exact
    Set.disjoint_left.mpr
      (fun m hmTail hmExceptional => hmTail.2 hmExceptional)

theorem Complex.logarithmicPhasePoissonFarTailSet_subset_outsideRange
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) :
    Complex.logarithmicPhasePoissonFarTailSet t a exceptional ⊆
      (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ := by
  intro m hm
  exact hm.1

theorem Complex.logarithmicPhasePoissonFarTail_union_outsideRangeExceptional_eq_outsideRange
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) :
    Complex.logarithmicPhasePoissonFarTailSet t a exceptional ∪
        Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
          t a exceptional =
      (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ := by
  ext m
  constructor
  · intro hm
    match hm with
    | Or.inl htail =>
        exact htail.1
    | Or.inr hexceptional =>
        exact hexceptional.1
  · intro hmoutside
    match Classical.em (m ∈ exceptional) with
    | Or.inl hmexceptional =>
        exact Or.inr ⟨hmoutside, hmexceptional⟩
    | Or.inr hmexceptional =>
        exact Or.inl ⟨hmoutside, hmexceptional⟩

theorem Complex.logarithmicPhasePoissonFarTail_disjoint_outsideRangeExceptional
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonFarTailSet t a exceptional)
      (Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
        t a exceptional) := by
  exact
    Set.disjoint_left.mpr
      (fun m htail hexceptional => htail.2 hexceptional.2)

theorem Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet_subset_exceptional
    (t : ℝ) (a : ℤ) (exceptional : Set ℤ) :
    Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
      t a exceptional ⊆ exceptional := by
  intro m hm
  exact hm.2

theorem Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget_nonneg
    (t : ℝ) (a b : ℤ) (exceptional : Set ℤ)
    (hfinite :
      (Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
        t a exceptional).Finite) :
    0 ≤ Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget
      t a b exceptional hfinite := by
  unfold Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget_le_card_mul
    (t : ℝ) (a b : ℤ) (exceptional : Set ℤ)
    (hfinite :
      (Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
        t a exceptional).Finite)
    (C : ℝ)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
          t a exceptional →
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C) :
    Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget
      t a b exceptional hfinite ≤
      ((hfinite.toFinset.card : ℕ) : ℝ) * C := by
  unfold Complex.logarithmicPhasePoissonOutsideRangeExceptionalBudget
  have hpointwise :
      (∑ m ∈ hfinite.toFinset,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
        ∑ m ∈ hfinite.toFinset, C := by
    exact
      Finset.sum_le_sum
        (fun m hm =>
          have hmset :
              m ∈ Complex.logarithmicPhasePoissonOutsideRangeExceptionalSet
                t a exceptional :=
            (Set.Finite.mem_toFinset hfinite).mp hm
          hbound m hmset)
  have hconstant :
      (∑ m ∈ hfinite.toFinset, C) =
        ((hfinite.toFinset.card : ℕ) : ℝ) * C := by
    exact Finset.sum_const_real_eq_card_mul hfinite.toFinset C
  exact hpointwise.trans_eq hconstant

theorem Complex.norm_logarithmicPhasePoissonFarTail_tsum_le_majorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (C : ℝ) (exceptional : Set ℤ)
    (hpacket :
      ∀ m : ℤ, m ∉ exceptional →
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ C * |(m : ℝ)| ^ (-2 : ℝ)) :
    ‖∑' m : Complex.logarithmicPhasePoissonFarTailSet t a exceptional,
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhasePoissonFarTailMajorant t a exceptional C := by
  have hsummable :=
    Complex.summable_logarithmicPhasePoissonFarTailMajorant
      t a exceptional C
  have hbound :
      ∀ m : Complex.logarithmicPhasePoissonFarTailSet t a exceptional,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤ C * |(m : ℝ)| ^ (-2 : ℝ) := by
    intro m
    exact hpacket m m.property.2
  exact
    Complex.norm_logarithmicPhase_packet_subtype_tsum_le_subtype_bound
      t a b
      (Complex.logarithmicPhasePoissonFarTailSet t a exceptional)
      (fun m : ℤ => C * |(m : ℝ)| ^ (-2 : ℝ))
      hbound hsummable

theorem Complex.logarithmicPhasePoisson_farTail_exists_inverseSquare_bound
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ C : ℝ, ∃ exceptional : Set ℤ,
      exceptional.Finite ∧
        ‖∑' m : Complex.logarithmicPhasePoissonFarTailSet t a exceptional,
            Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖ ≤
          Complex.logarithmicPhasePoissonFarTailMajorant t a exceptional C := by
  match
      Complex.logarithmicPhase_integerBlockFourierPacket_sequence_finite_exception_inverse_square
        t a b ha hab with
  | ⟨C, exceptional, hexceptional, hpacket⟩ =>
      exact
        Exists.intro C
          (Exists.intro exceptional
            (And.intro hexceptional
              (Complex.norm_logarithmicPhasePoissonFarTail_tsum_le_majorant
                t a b ha hab C exceptional hpacket)))

end
end LFunctions
end Boundary
