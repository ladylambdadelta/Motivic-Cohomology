import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBudgetArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointFirstDerivative

/-!
# Arithmetic closure for the direct logarithmic Poisson budget

The direct Poisson owner supplies the actual analytic components.  This file
owns only their final numerical assembly.  The public long branch will consume
the theorem here after the three component estimates have been proved from
stationary-window and far-tail geometry.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseDirectPoissonTarget
    (t : ℝ) (b : ℤ) : ℝ :=
  ((b : ℝ) + 1) / ‖t‖ + Real.sqrt (1 + ‖t‖)

theorem Real.logarithmicPhase_twenty_forty_targets_le_sixty
    (E : ℝ) :
    20 * E + 40 * E ≤ 60 * E := by
  have htwenty_forty : (20 + 40 : ℝ) = 60 := by
    have hnat : (20 + 40 : ℕ) = 60 :=
      rfl
    exact
      Eq.trans
        (Nat.cast_add 20 40).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ)) hnat)
          Nat.cast_ofNat)
  have hsum :
      20 * E + 40 * E = (20 + 40 : ℝ) * E :=
    (add_mul 20 40 E).symm
  have htarget :
      (20 + 40 : ℝ) * E = 60 * E :=
    congrArg (fun value : ℝ => value * E) htwenty_forty
  exact le_of_eq (Eq.trans hsum htarget)

theorem Real.logarithmicPhase_twenty_twenty_forty_targets_le_eighty
    (E : ℝ) :
    20 * E + 20 * E + 40 * E ≤ 80 * E := by
  have hleft :
      20 * E + 20 * E + 40 * E =
        20 * E + (20 * E + 40 * E) :=
    add_assoc (20 * E) (20 * E) (40 * E)
  have hsixty :
      20 * E + 40 * E ≤ 60 * E :=
    Real.logarithmicPhase_twenty_forty_targets_le_sixty E
  have hsum :
      20 * E + (20 * E + 40 * E) ≤ 20 * E + 60 * E :=
    add_le_add_left hsixty (20 * E)
  have heighty :
      20 * E + 60 * E ≤ 80 * E :=
    Real.logarithmicPhase_twenty_sixty_targets_le_eighty E
  exact
    le_trans
      (le_of_eq hleft)
      (le_trans hsum heighty)

theorem Complex.logarithmicPhase_integerBlock_norm_le_eightyTarget_of_directPoisson_components
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius)
    (hinterior :
      Complex.logarithmicPhasePoissonInteriorBudget t a b radius ≤
        20 * Real.logarithmicPhaseDirectPoissonTarget t b)
    (hendpoint :
      Complex.logarithmicPhasePoissonEndpointBudget t a b radius ≤
        20 * Real.logarithmicPhaseDirectPoissonTarget t b)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤
        40 * Real.logarithmicPhaseDirectPoissonTarget t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseDirectPoissonTarget t b := by
  have hcomponents :=
    Complex.logarithmicPhase_integerBlock_norm_le_of_directBudget_components
      t ht ht_nonneg a b ha hab radius
      (20 * Real.logarithmicPhaseDirectPoissonTarget t b)
      (20 * Real.logarithmicPhaseDirectPoissonTarget t b)
      (40 * Real.logarithmicPhaseDirectPoissonTarget t b)
      hradius hinterior hendpoint hinactive
  have htarget :=
    Real.logarithmicPhase_twenty_twenty_forty_targets_le_eighty
      (Real.logarithmicPhaseDirectPoissonTarget t b)
  exact le_trans hcomponents htarget

theorem Complex.logarithmicPhase_integerBlock_norm_le_eightyTarget_of_canonicalPoisson_components
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hinterior :
      Complex.logarithmicPhasePoissonCanonicalInteriorBudget t a b ≤
        20 * Real.logarithmicPhaseDirectPoissonTarget t b)
    (hendpoint :
      Complex.logarithmicPhasePoissonCanonicalEndpointBudget t a b ≤
        20 * Real.logarithmicPhaseDirectPoissonTarget t b)
    (hinactive :
      Complex.logarithmicPhasePoissonInactiveBudget t a b ≤
        40 * Real.logarithmicPhaseDirectPoissonTarget t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseDirectPoissonTarget t b := by
  have hcomponents :=
    Complex.logarithmicPhase_integerBlock_norm_le_of_canonicalPoisson_components
      t ht ht_nonneg a b ha hab
      (20 * Real.logarithmicPhaseDirectPoissonTarget t b)
      (20 * Real.logarithmicPhaseDirectPoissonTarget t b)
      (40 * Real.logarithmicPhaseDirectPoissonTarget t b)
      hinterior hendpoint hinactive
  have htarget :=
    Real.logarithmicPhase_twenty_twenty_forty_targets_le_eighty
      (Real.logarithmicPhaseDirectPoissonTarget t b)
  exact le_trans hcomponents htarget

theorem Real.logarithmicPhaseDirectPoissonTarget_eq
    (t : ℝ) (b : ℤ) :
    Real.logarithmicPhaseDirectPoissonTarget t b =
      ((b : ℝ) + 1) / ‖t‖ + Real.sqrt (1 + ‖t‖) :=
  rfl

theorem Real.logarithmicPhaseDirectPoissonTarget_nonneg
    (t : ℝ) (b : ℤ)
    (ht : 0 < ‖t‖) (hb : 0 ≤ (b : ℝ)) :
    0 ≤ Real.logarithmicPhaseDirectPoissonTarget t b := by
  unfold Real.logarithmicPhaseDirectPoissonTarget
  have hnum : 0 ≤ (b : ℝ) + 1 :=
    add_nonneg hb zero_le_one
  have hquot : 0 ≤ ((b : ℝ) + 1) / ‖t‖ :=
    div_nonneg hnum (le_of_lt ht)
  have hsqrt : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg _
  exact add_nonneg hquot hsqrt

/-- The direct Poisson scale contains a full unit once the logarithmic
frequency is in the global long-branch range.  This is the arithmetic bridge
that absorbs fixed cutoff-crossing and finite-transition constants. -/
theorem Real.one_le_logarithmicPhaseDirectPoissonTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖) (hb : 0 ≤ (b : ℝ)) :
    (1 : ℝ) ≤ Real.logarithmicPhaseDirectPoissonTarget t b := by
  unfold Real.logarithmicPhaseDirectPoissonTarget
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hnumerator : 0 ≤ (b : ℝ) + 1 :=
    add_nonneg hb zero_le_one
  have hquotient : 0 ≤ ((b : ℝ) + 1) / ‖t‖ :=
    div_nonneg hnumerator (le_of_lt ht_pos)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) :=
    Real.logarithmicPhase_one_le_sqrt_one_add_norm t ht
  exact
    le_trans
      (le_add_of_nonneg_left hquotient)
      (add_le_add_left hsqrt (((b : ℝ) + 1) / ‖t‖))

theorem Real.two_le_two_mul_logarithmicPhaseDirectPoissonTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖) (hb : 0 ≤ (b : ℝ)) :
    (2 : ℝ) ≤ 2 * Real.logarithmicPhaseDirectPoissonTarget t b := by
  have hone : (1 : ℝ) ≤ Real.logarithmicPhaseDirectPoissonTarget t b :=
    Real.one_le_logarithmicPhaseDirectPoissonTarget t b ht hb
  have htwo_eq : (2 : ℝ) = 2 * 1 :=
    (mul_one 2).symm
  have hmul : 2 * 1 ≤ 2 * Real.logarithmicPhaseDirectPoissonTarget t b :=
    mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg 2)
  exact le_trans (le_of_eq htwo_eq) hmul

theorem Real.four_div_three_le_two
    : (4 : ℝ) / 3 ≤ 2 := by
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hsix_eq : (2 : ℝ) * 3 = 6 := by
    have hnat : (2 * 3 : ℕ) = 6 :=
      rfl
    exact
      Eq.trans
        (Nat.cast_mul 2 3).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ)) hnat)
          Nat.cast_ofNat)
  have hfour_le_six : (4 : ℝ) ≤ 6 := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      Nat.cast_nonneg 2
    have hfour_eq : (4 : ℝ) = 2 + 2 := by
      exact (Nat.cast_add 2 2).symm
    have hsix_sum : (6 : ℝ) = 4 + 2 := by
      have hnat : (4 + 2 : ℕ) = 6 :=
        rfl
      exact
        Eq.trans
          (Nat.cast_add 4 2).symm
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat)
    calc
      (4 : ℝ) = 2 + 2 := hfour_eq
      _ ≤ 4 + 2 := add_le_add_right (show (2 : ℝ) ≤ 4 from
        le_add_of_nonneg_right htwo_nonneg) 2
      _ = 6 := hsix_sum.symm
  exact
    (div_le_iff₀ hthree_pos).mpr
      (le_trans hfour_le_six (le_of_eq hsix_eq.symm))

theorem Real.four_div_three_le_two_mul_logarithmicPhaseDirectPoissonTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖) (hb : 0 ≤ (b : ℝ)) :
    (4 : ℝ) / 3 ≤ 2 * Real.logarithmicPhaseDirectPoissonTarget t b := by
  exact
    le_trans
      Real.four_div_three_le_two
      (Real.two_le_two_mul_logarithmicPhaseDirectPoissonTarget t b ht hb)

theorem Real.eight_div_three_le_four_mul_logarithmicPhaseDirectPoissonTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖) (hb : 0 ≤ (b : ℝ)) :
    (8 : ℝ) / 3 ≤ 4 * Real.logarithmicPhaseDirectPoissonTarget t b := by
  have hdouble : (8 : ℝ) / 3 = 2 * ((4 : ℝ) / 3) := by
    have height : (8 : ℝ) = 2 * 4 := by
      have hnat : (2 * 4 : ℕ) = 8 :=
        rfl
      exact
        Eq.trans
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat).symm
            (Nat.cast_mul 2 4))
          rfl
    calc
      (8 : ℝ) / 3 = (2 * 4 : ℝ) / 3 :=
        congrArg (fun value : ℝ => value / 3) height
      _ = 2 * ((4 : ℝ) / 3) :=
        mul_div_assoc 2 4 3
  have hcrossing : (4 : ℝ) / 3 ≤
      2 * Real.logarithmicPhaseDirectPoissonTarget t b :=
    Real.four_div_three_le_two_mul_logarithmicPhaseDirectPoissonTarget
      t b ht hb
  have hdouble_bound :
      2 * ((4 : ℝ) / 3) ≤
        2 * (2 * Real.logarithmicPhaseDirectPoissonTarget t b) :=
    mul_le_mul_of_nonneg_left hcrossing (Nat.cast_nonneg 2)
  have hassoc :
      2 * (2 * Real.logarithmicPhaseDirectPoissonTarget t b) =
        4 * Real.logarithmicPhaseDirectPoissonTarget t b := by
    have hfour : (2 * 2 : ℝ) = 4 := by
      have hnat : (2 * 2 : ℕ) = 4 :=
        rfl
      exact
        Eq.trans
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat).symm
            (Nat.cast_mul 2 2))
          rfl
    calc
      2 * (2 * Real.logarithmicPhaseDirectPoissonTarget t b) =
          (2 * 2 : ℝ) * Real.logarithmicPhaseDirectPoissonTarget t b :=
        mul_assoc 2 2 (Real.logarithmicPhaseDirectPoissonTarget t b)
      _ = 4 * Real.logarithmicPhaseDirectPoissonTarget t b := by
        exact congrArg
          (fun value : ℝ => value * Real.logarithmicPhaseDirectPoissonTarget t b)
          hfour
  exact le_trans (le_of_eq hdouble) (le_trans hdouble_bound (le_of_eq hassoc))

end
end LFunctions
end Boundary
