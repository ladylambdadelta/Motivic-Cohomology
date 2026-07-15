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
      Complex.logarithmicPhasePoissonPositiveTailModes := by
  classical
  exact if hfar : (m : ℤ) ∈
        Complex.logarithmicPhasePoissonFarNegativeModes t a then
      Sum.inl ⟨(m : ℤ), hfar⟩
    else
      Sum.inr ⟨(m : ℤ),
        Or.resolve_left
          (Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
            t a m)
          hfar⟩

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
  classical
  by_cases hfar : (m : ℤ) ∈
      Complex.logarithmicPhasePoissonFarNegativeModes t a
  · have hselected :
        Complex.logarithmicPhaseOutsideToTailSum t a m =
          Sum.inl ⟨(m : ℤ), hfar⟩ := by
      unfold Complex.logarithmicPhaseOutsideToTailSum
      exact dif_pos hfar
    exact Eq.trans
      (congrArg
        (Sum.elim
          (fun n : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
            (n : ℤ))
          (fun n : Complex.logarithmicPhasePoissonPositiveTailModes =>
            (n : ℤ)))
        hselected)
      rfl
  · have hselected :
        Complex.logarithmicPhaseOutsideToTailSum t a m =
          Sum.inr ⟨(m : ℤ),
            Or.resolve_left
              (Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
                t a m)
              hfar⟩ := by
      unfold Complex.logarithmicPhaseOutsideToTailSum
      exact dif_neg hfar
    exact Eq.trans
      (congrArg
        (Sum.elim
          (fun n : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
            (n : ℤ))
          (fun n : Complex.logarithmicPhasePoissonPositiveTailModes =>
            (n : ℤ)))
        hselected)
      rfl

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
  classical
  match m with
  | Sum.inl n =>
      have hselected :
          Complex.logarithmicPhaseOutsideToTailSum t a
              (Complex.logarithmicPhaseTailSumToOutside t a (Sum.inl n)) =
            Sum.inl ⟨(n : ℤ), n.property⟩ := by
        unfold Complex.logarithmicPhaseOutsideToTailSum
        exact dif_pos n.property
      exact Eq.trans hselected
        (congrArg Sum.inl (Subtype.ext rfl))
  | Sum.inr n =>
      have hnotFar : ¬ (n : ℤ) ∈
          Complex.logarithmicPhasePoissonFarNegativeModes t a :=
        fun hfar =>
          have hlower :=
            Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha
          have hnegative : (n : ℤ) < 0 :=
            lt_of_lt_of_le hfar hlower
          not_lt_of_ge n.property.le hnegative
      have hselected :
          Complex.logarithmicPhaseOutsideToTailSum t a
              (Complex.logarithmicPhaseTailSumToOutside t a (Sum.inr n)) =
            Sum.inr ⟨(n : ℤ),
              Or.resolve_left
                (Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
                  t a
                  (Complex.logarithmicPhaseTailSumToOutside t a (Sum.inr n)))
                hnotFar⟩ := by
        unfold Complex.logarithmicPhaseOutsideToTailSum
        exact dif_neg hnotFar
      exact Eq.trans hselected
        (congrArg Sum.inr (Subtype.ext rfl))

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
