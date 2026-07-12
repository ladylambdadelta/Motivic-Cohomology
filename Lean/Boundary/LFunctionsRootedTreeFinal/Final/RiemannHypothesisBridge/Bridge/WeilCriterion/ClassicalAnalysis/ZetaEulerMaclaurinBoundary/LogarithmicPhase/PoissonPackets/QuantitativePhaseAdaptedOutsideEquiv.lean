import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedComplementBudget

/-!
# Outside-range modes as a sum of two tail subtypes

The exact complement characterization induces an equivalence from the
outside-range subtype to the sum of the far-negative and positive subtypes.
This owner supplies the reindexing used by the replacement complement budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseOutsideToTailSum
    (t : ℝ) (a : ℤ)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes :=
  match Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
      t a m with
  | Or.inl hfar => Sum.inl ⟨(m : ℤ), hfar⟩
  | Or.inr hpositive => Sum.inr ⟨(m : ℤ), hpositive⟩

def Complex.logarithmicPhaseTailSumToOutside
    (t : ℝ) (a : ℤ) :
    Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes →
    {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}
  | Sum.inl m =>
      ⟨(m : ℤ),
        Complex.logarithmicPhasePoissonFarNegative_not_mem_modeRange t a m⟩
  | Sum.inr m =>
      ⟨(m : ℤ),
        Complex.logarithmicPhasePoissonPositive_not_mem_modeRange t a m⟩

theorem Complex.logarithmicPhaseOutsideToTailSum_value
    (t : ℝ) (a : ℤ)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    Sum.elim
      (fun n : Complex.logarithmicPhasePoissonFarNegativeModes t a => (n : ℤ))
      (fun n : Complex.logarithmicPhasePoissonPositiveTailModes => (n : ℤ))
      (Complex.logarithmicPhaseOutsideToTailSum t a m) = (m : ℤ) := by
  unfold Complex.logarithmicPhaseOutsideToTailSum
  match Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
      t a m with
  | Or.inl hfar => exact rfl
  | Or.inr hpositive => exact rfl

theorem Complex.logarithmicPhaseTailSumToOutside_value
    (t : ℝ) (a : ℤ)
    (m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes) :
    (Complex.logarithmicPhaseTailSumToOutside t a m : ℤ) =
      Sum.elim
        (fun n : Complex.logarithmicPhasePoissonFarNegativeModes t a => (n : ℤ))
        (fun n : Complex.logarithmicPhasePoissonPositiveTailModes => (n : ℤ)) m := by
  match m with
  | Sum.inl n => exact rfl
  | Sum.inr n => exact rfl

theorem Complex.logarithmicPhaseOutsideToTailSum_leftInverse
    (t : ℝ) (a : ℤ)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    Complex.logarithmicPhaseTailSumToOutside t a
      (Complex.logarithmicPhaseOutsideToTailSum t a m) = m := by
  exact Subtype.ext
    (Eq.trans
      (Complex.logarithmicPhaseTailSumToOutside_value t a
        (Complex.logarithmicPhaseOutsideToTailSum t a m))
      (Complex.logarithmicPhaseOutsideToTailSum_value t a m))

theorem Complex.logarithmicPhaseOutsideToTailSum_rightInverse
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a)
    (m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseOutsideToTailSum t a
      (Complex.logarithmicPhaseTailSumToOutside t a m) = m := by
  match m with
  | Sum.inl n =>
      have hfar :
          ((Complex.logarithmicPhaseTailSumToOutside t a (Sum.inl n) :
            {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) : ℤ) ∈
            Complex.logarithmicPhasePoissonFarNegativeModes t a := n.property
      unfold Complex.logarithmicPhaseOutsideToTailSum
      match Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
          t a (Complex.logarithmicPhaseTailSumToOutside t a (Sum.inl n)) with
      | Or.inl hselected => exact congrArg Sum.inl (Subtype.ext rfl)
      | Or.inr hpositive =>
          exact False.elim
            (Set.disjoint_left.mp
              (Complex.logarithmicPhasePoissonFarNegative_positive_disjoint
                t a ha)
              _ hfar hpositive)
  | Sum.inr n =>
      unfold Complex.logarithmicPhaseOutsideToTailSum
      match Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
          t a (Complex.logarithmicPhaseTailSumToOutside t a (Sum.inr n)) with
      | Or.inl hfar =>
          have hlower := Complex.logarithmicPhasePoissonModeRangeLower_le_zero
            t ha
          have hnegative :
              ((Complex.logarithmicPhaseTailSumToOutside t a (Sum.inr n) :
                {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) : ℤ) < 0 :=
            lt_of_lt_of_le hfar hlower
          exact False.elim (not_lt_of_ge n.property.le hnegative)
      | Or.inr hselected => exact congrArg Sum.inr (Subtype.ext rfl)

def Complex.logarithmicPhaseOutsideEquivTailSum
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a} ≃
      Sum
        (Complex.logarithmicPhasePoissonFarNegativeModes t a)
        Complex.logarithmicPhasePoissonPositiveTailModes where
  toFun := Complex.logarithmicPhaseOutsideToTailSum t a
  invFun := Complex.logarithmicPhaseTailSumToOutside t a
  left_inv := Complex.logarithmicPhaseOutsideToTailSum_leftInverse t a
  right_inv := Complex.logarithmicPhaseOutsideToTailSum_rightInverse t a ha

end
end LFunctions
end Boundary
