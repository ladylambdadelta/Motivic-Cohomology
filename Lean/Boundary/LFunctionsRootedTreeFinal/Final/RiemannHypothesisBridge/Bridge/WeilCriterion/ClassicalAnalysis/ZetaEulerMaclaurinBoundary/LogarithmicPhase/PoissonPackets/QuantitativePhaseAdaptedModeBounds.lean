import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPacketClosedBound

/-!
# Closed packet bounds for the three nonstationary mode classes

Positive modes are globally nonstationary.  Negative modes are nonstationary
on the support when their stationary center lies beyond its left or right
endpoint.  The corresponding endpoint gaps feed the deterministic packet
majorant without auxiliary witnesses.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Interval

theorem Complex.logarithmicPhasePositiveModeGap_pos
    (m : ℤ) (hm : 0 < m) :
    0 < Complex.logarithmicPhasePositiveModeGap m := by
  have htwoPi : 0 < 2 * Real.pi :=
    mul_pos zero_lt_two Real.pi_pos
  have hmReal : 0 < (m : ℝ) := Int.cast_pos.mpr hm
  exact mul_pos htwoPi hmReal

theorem Complex.norm_logarithmicPhasePositiveModePacket_le
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhasePositiveModeClosedMajorant t a b m := by
  have hgap : 0 < Complex.logarithmicPhasePositiveModeGap m :=
    Complex.logarithmicPhasePositiveModeGap_pos m hm
  have hmNonneg : 0 ≤ m := le_of_lt hm
  have hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
      Complex.logarithmicPhaseQuantitativeSupportRight b]],
      Complex.logarithmicPhasePositiveModeGap m ≤
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    fun x hx =>
      Complex.logarithmicPhasePositiveModeDerivative_gap
        t x m
        (Complex.logarithmicPhaseQuantitativeSupport_mem_positive
          a b ha hab hx)
        hmNonneg
  exact Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    t a b m (Complex.logarithmicPhasePositiveModeGap m)
    ha hab hgap hlower

theorem Complex.logarithmicPhaseLeftInactiveGap_pos_of_strict
    (t : ℝ) (m : ℤ) (left : ℝ)
    (hstrict : ‖t‖ / left < 2 * Real.pi * (-(m : ℝ))) :
    0 < Complex.logarithmicPhaseLeftInactiveGap t m left := by
  exact sub_pos.mpr hstrict

theorem Complex.logarithmicPhaseRightInactiveGap_pos_of_strict
    (t : ℝ) (m : ℤ) (right : ℝ)
    (hstrict : 2 * Real.pi * (-(m : ℝ)) < ‖t‖ / right) :
    0 < Complex.logarithmicPhaseRightInactiveGap t m right := by
  exact sub_pos.mpr hstrict

theorem Complex.norm_logarithmicPhaseLeftInactiveModePacket_le
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hstrict :
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
        2 * Real.pi * (-(m : ℝ))) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m := by
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  let gap : ℝ := Complex.logarithmicPhaseLeftInactiveGap t m left
  have hleftPos : 0 < left :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hleftRight : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hgap : 0 < gap :=
    Complex.logarithmicPhaseLeftInactiveGap_pos_of_strict t m left hstrict
  have hIcc : ∀ x ∈ [[left, right]], x ∈ Set.Icc left right :=
    fun x hx =>
      Eq.mp
        (congrArg (fun support : Set ℝ => x ∈ support)
          (Set.uIcc_of_le hleftRight))
        hx
  have hlower : ∀ x ∈ [[left, right]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseLeftInactiveDerivative_gap
        t x left m hleftPos (hIcc x hx).1 hgap.le
  exact Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    t a b m gap ha hab hgap hlower

theorem Complex.norm_logarithmicPhaseRightInactiveModePacket_le
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hstrict :
      2 * Real.pi * (-(m : ℝ)) <
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseRightInactiveClosedMajorant t a b m := by
  let left : ℝ := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right : ℝ := Complex.logarithmicPhaseQuantitativeSupportRight b
  let gap : ℝ := Complex.logarithmicPhaseRightInactiveGap t m right
  have hleftRight : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hgap : 0 < gap :=
    Complex.logarithmicPhaseRightInactiveGap_pos_of_strict t m right hstrict
  have hIcc : ∀ x ∈ [[left, right]], x ∈ Set.Icc left right :=
    fun x hx =>
      Eq.mp
        (congrArg (fun support : Set ℝ => x ∈ support)
          (Set.uIcc_of_le hleftRight))
        hx
  have hlower : ∀ x ∈ [[left, right]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    fun x hx =>
      Complex.logarithmicPhaseRightInactiveDerivative_gap
        t x right m
        (lt_of_lt_of_le
          (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha)
          (hIcc x hx).1)
        (hIcc x hx).2 hgap.le
  exact Complex.norm_logarithmicPhaseAdaptedPacket_le_closedMajorant
    t a b m gap ha hab hgap hlower

end
end LFunctions
end Boundary
