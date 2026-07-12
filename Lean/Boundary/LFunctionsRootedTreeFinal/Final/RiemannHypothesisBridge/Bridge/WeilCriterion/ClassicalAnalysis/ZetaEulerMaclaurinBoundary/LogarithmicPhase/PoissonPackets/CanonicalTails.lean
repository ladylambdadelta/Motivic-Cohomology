import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalCentralWindow

/-!
# Canonical stationary tails

The principal logarithmic packet is resolved into its left nonstationary tail,
central stationary window, and right nonstationary tail. The two tail bounds
are the explicit reciprocal-coefficient estimates at the canonical window
endpoints.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonCanonicalLeftTail
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in (a : ℝ)..Complex.logarithmicPhasePoissonCanonicalWindowLeft t m,
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m) x

def Complex.logarithmicPhasePoissonCanonicalRightTail
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in Complex.logarithmicPhasePoissonCanonicalWindowRight t m..(b : ℝ),
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m) x

def Complex.logarithmicPhasePoissonCanonicalLeftTailMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  2 * ((2 * Real.pi * (-(m : ℝ))) *
    (Complex.logarithmicPhaseFourierStationaryPoint t m -
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) /
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)⁻¹ +
    (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m - (a : ℝ)) •
      ((‖t‖ / (a : ℝ) ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) /
            Complex.logarithmicPhasePoissonCanonicalWindowLeft t m) ^ 2)

def Complex.logarithmicPhasePoissonCanonicalRightTailMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  2 * ((2 * Real.pi * (-(m : ℝ))) *
    (Complex.logarithmicPhasePoissonCanonicalWindowRight t m -
      Complex.logarithmicPhaseFourierStationaryPoint t m) /
      (b : ℝ))⁻¹ +
    ((b : ℝ) - Complex.logarithmicPhasePoissonCanonicalWindowRight t m) •
      ((‖t‖ /
        Complex.logarithmicPhasePoissonCanonicalWindowRight t m ^ 2) /
        ((2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhasePoissonCanonicalWindowRight t m -
            Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (b : ℝ)) ^ 2)

def Complex.logarithmicPhasePoissonCanonicalStationaryMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  4 / 3 +
    Complex.logarithmicPhasePoissonCanonicalLeftTailMajorant t a b m +
      Complex.logarithmicPhasePoissonCanonicalWindowWidth t m +
        Complex.logarithmicPhasePoissonCanonicalRightTailMajorant t a b m

theorem Complex.logarithmicPhasePoissonCanonicalWindowLeft_pos_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m := by
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem t a b m hm
  have ha_pos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  exact lt_of_lt_of_le ha_pos hbounds.1

theorem Complex.norm_logarithmicPhasePoissonCanonicalLeftTail_le_majorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalLeftTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalLeftTailMajorant t a b m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem t a b m hm
  have hleft_pos :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowLeft t m :=
    Complex.logarithmicPhasePoissonCanonicalWindowLeft_pos_of_mem
      t ht ha hm
  have hleft_right :
      (a : ℝ) ≤ Complex.logarithmicPhasePoissonCanonicalWindowLeft t m :=
    hbounds.1
  have hright_block :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m ≤ (b : ℝ) :=
    le_trans
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m)
      (le_trans
        (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m)
        hbounds.2)
  have hcenter :
      Complex.logarithmicPhasePoissonCanonicalWindowLeft t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowLeft
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_left_lt_center
        t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_left_nonstationary_tail_explicit
      t ht ht_nonneg a b m (a : ℝ)
      (Complex.logarithmicPhasePoissonCanonicalWindowLeft t m)
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha))
      le_rfl hright_block hleft_right hcenter hmem.2.1

theorem Complex.norm_logarithmicPhasePoissonCanonicalRightTail_le_majorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalRightTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalRightTailMajorant t a b m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhasePoissonCanonicalWindow_bounds_of_mem t a b m hm
  have hleft_block :
      (a : ℝ) ≤ Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    le_trans hbounds.1
      (le_trans
        (Complex.logarithmicPhasePoissonCanonicalWindowLeft_le_center t m)
        (Complex.logarithmicPhasePoissonCanonicalWindowCenter_le_right t m))
  have hleft_pos :
      0 < Complex.logarithmicPhasePoissonCanonicalWindowRight t m :=
    lt_of_lt_of_le
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha))
      hleft_block
  have hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhasePoissonCanonicalWindowRight t m := by
    unfold Complex.logarithmicPhasePoissonCanonicalWindowRight
    exact
      Complex.logarithmicPhasePoissonCanonicalRadius_center_lt_right
        t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_realOscillation_le_right_nonstationary_tail_explicit
      t ht ht_nonneg a b m
      (Complex.logarithmicPhasePoissonCanonicalWindowRight t m) (b : ℝ)
      hleft_pos hleft_block le_rfl hbounds.2 hcenter hmem.2.1

/-- The existing three-piece packet proof, specialized to the canonical
stationary radius, has exactly the named central and tail majorants above. -/
theorem Complex.norm_integerBlockFourierPacket_le_canonicalStationaryMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalStationaryMajorant t a b m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hradius :
      0 < Complex.logarithmicPhasePoissonCanonicalRadius t m :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hmem.2.1
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_active_stationary_explicit
      t ht ht_nonneg a b m ha hab hmem.2.1
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)
      rfl hradius hmem.2.2.1 hmem.2.2.2
  exact hpacket

end
end LFunctions
end Boundary
