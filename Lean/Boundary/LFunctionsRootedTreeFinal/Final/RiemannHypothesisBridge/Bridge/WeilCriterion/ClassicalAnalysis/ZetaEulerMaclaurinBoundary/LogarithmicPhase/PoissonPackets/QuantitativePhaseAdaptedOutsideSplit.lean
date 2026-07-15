import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPositiveTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeInactiveAndFarTail

/-!
# Exact split of the canonical outside-range modes

Since the canonical range is the integer interval from its floor-defined lower
endpoint through zero, its complement is the disjoint union of a far-negative
ray and the positive ray.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePoissonFarNegativeModes
    (t : ℝ) (a : ℤ) : Set ℤ :=
  {m : ℤ | m < Complex.logarithmicPhasePoissonModeRangeLower t a}

theorem Complex.mem_logarithmicPhasePoissonFarNegativeModes_iff
    (t : ℝ) (a m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonFarNegativeModes t a ↔
      m < Complex.logarithmicPhasePoissonModeRangeLower t a := by
  exact Iff.rfl

theorem Complex.logarithmicPhasePoissonFarNegative_positive_disjoint
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a) :
    Disjoint
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes := by
  exact Set.disjoint_left.mpr
    (fun m hmFar hmPositive =>
      have hlower := Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha
      have hmNegative : m < 0 := lt_of_lt_of_le hmFar hlower
      have hcycle : m < m := lt_trans hmNegative hmPositive
      lt_irrefl m hcycle)

theorem Complex.not_mem_logarithmicPhasePoissonModeRange_iff
    (t : ℝ) (a m : ℤ) :
    m ∉ Complex.logarithmicPhasePoissonModeRange t a ↔
      m < Complex.logarithmicPhasePoissonModeRangeLower t a ∨ 0 < m := by
  have hmem := Complex.mem_logarithmicPhasePoissonModeRange_iff t a m
  exact Iff.intro
    (fun hm =>
      match lt_trichotomy m
          (Complex.logarithmicPhasePoissonModeRangeLower t a) with
      | Or.inl hmLower => Or.inl hmLower
      | Or.inr hremaining =>
          have hlower :
              Complex.logarithmicPhasePoissonModeRangeLower t a ≤ m :=
            Or.elim hremaining
              (fun heq => le_of_eq heq.symm)
              (fun hlt => hlt.le)
          match lt_trichotomy m 0 with
          | Or.inl hmZero =>
              have hmRange := hmem.mpr ⟨hlower, hmZero.le⟩
              False.elim (hm hmRange)
          | Or.inr hzeroRemaining =>
              match hzeroRemaining with
              | Or.inl hmZeroEq =>
                  have hmRange := hmem.mpr ⟨hlower, le_of_eq hmZeroEq⟩
                  False.elim (hm hmRange)
              | Or.inr hmPositive => Or.inr hmPositive)
    (fun hm hmRange =>
      have hborders := hmem.mp hmRange
      match hm with
      | Or.inl hmFar => (not_lt_of_ge hborders.1) hmFar
      | Or.inr hmPositive => (not_lt_of_ge hborders.2) hmPositive)

theorem Complex.logarithmicPhasePoissonModeRange_complement_eq_farNegative_union_positive
    (t : ℝ) (a : ℤ) :
    ((Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ) =
      Complex.logarithmicPhasePoissonFarNegativeModes t a ∪
        Complex.logarithmicPhasePoissonPositiveTailModes := by
  exact Set.ext (fun m =>
    Iff.trans Iff.rfl
      (Complex.not_mem_logarithmicPhasePoissonModeRange_iff t a m))

theorem Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
    (t : ℝ) (a : ℤ)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    (m : ℤ) ∈ Complex.logarithmicPhasePoissonFarNegativeModes t a ∨
      (m : ℤ) ∈ Complex.logarithmicPhasePoissonPositiveTailModes := by
  exact (Complex.not_mem_logarithmicPhasePoissonModeRange_iff t a m).mp
    m.property

theorem Complex.logarithmicPhasePoissonFarNegative_not_mem_modeRange
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    (m : ℤ) ∉ Complex.logarithmicPhasePoissonModeRange t a := by
  exact (Complex.not_mem_logarithmicPhasePoissonModeRange_iff t a m).mpr
    (Or.inl m.property)

theorem Complex.logarithmicPhasePoissonPositive_not_mem_modeRange
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    (m : ℤ) ∉ Complex.logarithmicPhasePoissonModeRange t a := by
  exact (Complex.not_mem_logarithmicPhasePoissonModeRange_iff t a m).mpr
    (Or.inr m.property)

end
end LFunctions
end Boundary
