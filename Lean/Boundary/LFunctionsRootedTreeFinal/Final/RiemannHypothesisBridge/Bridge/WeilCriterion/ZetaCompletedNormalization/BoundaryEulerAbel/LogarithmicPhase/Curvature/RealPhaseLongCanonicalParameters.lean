import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveParameters
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongSpanRange

/-!
# Canonical long-branch additive resonance parameters

This file owns the finite square-budget arithmetic for the canonical
all-integer monotone-curvature resonance decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace Real

/-- The canonical span-local lower range for one positive long-branch Weyl
shift. -/
abbrev logarithmicPhaseRealPhase_longShiftSpanLo
    (t : ℝ)
    (a b h : ℕ) : ℝ :=
  min
    (Real.logarithmicPhaseRealPhase_spanIncrementLo t (b - h) h)
    (Real.logarithmicPhaseRealPhase_spanIncrementHi t a h)

/-- The canonical span-local upper range for one positive long-branch Weyl
shift. -/
abbrev logarithmicPhaseRealPhase_longShiftSpanHi
    (t : ℝ)
    (a h : ℕ) : ℝ :=
  Real.logarithmicPhaseRealPhase_spanIncrementHi t a h

/-- Canonical range-counted resonant-center cardinality for one long Weyl
shift. -/
abbrev logarithmicPhaseRealPhase_longResonanceCenterCount
    (t : ℝ)
    (a b h : ℕ) : ℝ :=
  ((Complex.realPhase_integerIncrementRangeActiveCenters
    (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
    (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
    (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card : ℝ)

/-- Canonical range-counted principal-strip center cardinality for one long
Weyl shift. -/
abbrev logarithmicPhaseRealPhase_longPrincipalCenterCount
    (t : ℝ)
    (a b h : ℕ) : ℝ :=
  ((Complex.realPhase_integerIncrementRangeActiveCenters
    (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
    (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
    Real.pi).card : ℝ)

/-- The canonical safe span lower endpoint is below the span upper endpoint. -/
theorem logarithmicPhaseRealPhase_longShiftSpanLo_le_hi
    (t : ℝ)
    (a b h : ℕ) :
    Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h ≤
      Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h := by
  exact
    min_le_right
      (Real.logarithmicPhaseRealPhase_spanIncrementLo t (b - h) h)
      (Real.logarithmicPhaseRealPhase_spanIncrementHi t a h)

/-- Resonant-center count for one long Weyl shift is bounded by the padded
span width. -/
theorem logarithmicPhaseRealPhase_longResonanceCenterCount_le_width_add_five
    (t : ℝ)
    {a b h : ℕ}
    (heta_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) :
    Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h ≤
      (((Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h +
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          (2 * Real.pi)) -
        ((Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h -
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          (2 * Real.pi)) + 5) := by
  exact
    Complex.realPhase_integerIncrementRangeActiveCenters_card_real_le_width_add_five
      (Real.logarithmicPhaseRealPhase_longShiftSpanLo_le_hi t a b h)
      heta_nonneg

/-- Principal-strip center count for one long Weyl shift is bounded by the
padded span width with thickness `π`. -/
theorem logarithmicPhaseRealPhase_longPrincipalCenterCount_le_width_add_five
    (t : ℝ)
    (a b h : ℕ) :
    Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h ≤
      (((Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h + Real.pi) /
          (2 * Real.pi)) -
        ((Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h - Real.pi) /
          (2 * Real.pi)) + 5) := by
  exact
    Complex.realPhase_integerIncrementRangeActiveCenters_card_real_le_width_add_five
      (Real.logarithmicPhaseRealPhase_longShiftSpanLo_le_hi t a b h)
      Real.pi_nonneg

/-- Shift-range specialization of the resonant-center count bound. -/
theorem logarithmicPhaseRealPhase_shiftRange_longResonanceCenterCount_le_width_add_five
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    (hh :
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) :
    Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h ≤
      (((Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h +
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          (2 * Real.pi)) -
        ((Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h -
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
          (2 * Real.pi)) + 5) := by
  exact
    Real.logarithmicPhaseRealPhase_longResonanceCenterCount_le_width_add_five
      t
      (le_of_lt
        (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
          t ht (b := b) h hh))

/-- Resonant-center counts are nonnegative. -/
theorem logarithmicPhaseRealPhase_longResonanceCenterCount_nonneg
    (t : ℝ)
    (a b h : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h := by
  exact Nat.cast_nonneg
    (Complex.realPhase_integerIncrementRangeActiveCenters
      (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
      (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card

/-- Principal-center counts are nonnegative. -/
theorem logarithmicPhaseRealPhase_longPrincipalCenterCount_nonneg
    (t : ℝ)
    (a b h : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h := by
  exact Nat.cast_nonneg
    (Complex.realPhase_integerIncrementRangeActiveCenters
      (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
      (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
      Real.pi).card

/-- Canonical first-derivative gap majorant for the additive all-integer
resonance decomposition on one Weyl shift. -/
abbrev logarithmicPhaseRealPhase_longAdditiveGapMajorant
    (t : ℝ)
    (b h : ℕ) : ℝ :=
  4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1) +
    4 * Real.pi * (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹

/-- The canonical additive first-derivative gap majorant is nonnegative on
every positive long Weyl shift. -/
theorem logarithmicPhaseRealPhase_longAdditiveGapMajorant_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b h : ℕ}
    (hh :
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖)) :
    0 ≤ Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant t b h := by
  have heta_pos :
      0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
      t ht (b := b) h hh
  have heta_inv_nonneg :
      0 ≤ (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
    inv_nonneg.mpr (le_of_lt heta_pos)
  have hfirst_inner :
      0 ≤ (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1 :=
    add_nonneg heta_inv_nonneg zero_le_one
  have hfirst :
      0 ≤ 4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1) :=
    mul_nonneg zero_le_four hfirst_inner
  have hfour_pi :
      0 ≤ 4 * Real.pi :=
    mul_nonneg zero_le_four Real.pi_nonneg
  have hsecond :
      0 ≤ 4 * Real.pi *
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
    mul_nonneg hfour_pi heta_inv_nonneg
  exact add_nonneg hfirst hsecond

/-- Canonical additive all-integer envelope contribution for one Weyl shift. -/
abbrev logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm
    (t : ℝ)
    (a b h : ℕ) : ℝ :=
  Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h *
      Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h +
    (((Complex.realPhase_integerIncrementRangeActiveCenters
        (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
        (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
        (Complex.realPhase_integerIncrementRangeActiveCenters
          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
          Real.pi).card + 1 : ℕ) : ℝ) *
      Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant t b h +
    1

/-- One canonical additive envelope term is nonnegative on every positive long
Weyl shift. -/
theorem logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    (hh :
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖))
    (hW_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h) :
    0 ≤ Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h := by
  have hC_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h :=
    Real.logarithmicPhaseRealPhase_longResonanceCenterCount_nonneg t a b h
  have hresonant :
      0 ≤
        Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h *
          Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
    mul_nonneg hC_nonneg hW_nonneg
  have hfamily_nonneg :
      0 ≤
        (((Complex.realPhase_integerIncrementRangeActiveCenters
            (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
            (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
              (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
              Real.pi).card + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg
      ((Complex.realPhase_integerIncrementRangeActiveCenters
          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
          (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
        (Complex.realPhase_integerIncrementRangeActiveCenters
          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
          Real.pi).card + 1)
  have hgap_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant t b h :=
    Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant_nonneg t ht hh
  have hgap_family :
      0 ≤
        (((Complex.realPhase_integerIncrementRangeActiveCenters
            (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
            (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
              (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
              Real.pi).card + 1 : ℕ) : ℝ) *
          Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant t b h :=
    mul_nonneg hfamily_nonneg hgap_nonneg
  exact add_nonneg (add_nonneg hresonant hgap_family) zero_le_one

/-- Canonical shifted-correlation envelope for the additive all-integer
monotone-curvature decomposition. -/
abbrev logarithmicPhaseRealPhase_longAdditiveEnvelope
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h

/-! The refined budget is owned componentwise.  These declarations deliberately
retain the three analytic sources instead of hiding them in the older combined
shifted-correlation envelope. -/

/-- One active-window budget term. -/
def logarithmicPhaseRealPhase_longActiveWindowTerm
    (centerCount windowMajorant : ℝ) : ℝ :=
  centerCount * windowMajorant

/-- One principal-strip crossing budget term. -/
def logarithmicPhaseRealPhase_longPrincipalStripCrossingTerm
    (resonanceCount principalCount eta : ℝ) : ℝ :=
  (resonanceCount + principalCount + 1) * (4 * (eta⁻¹ + 1))

/-- One connected complement-gap budget term, including its terminal sample. -/
def logarithmicPhaseRealPhase_longComplementGapTerm
    (resonanceCount principalCount eta : ℝ) : ℝ :=
  (resonanceCount + principalCount + 1) * (4 * Real.pi * eta⁻¹) + 1

/-- Active-window terms are monotone in both nonnegative inputs. -/
theorem logarithmicPhaseRealPhase_longActiveWindowTerm_mono
    {C₁ C₂ W₁ W₂ : ℝ}
    (hC : C₁ ≤ C₂)
    (hW : W₁ ≤ W₂)
    (hC₂_nonneg : 0 ≤ C₂)
    (hW₁_nonneg : 0 ≤ W₁) :
    Real.logarithmicPhaseRealPhase_longActiveWindowTerm C₁ W₁ ≤
      Real.logarithmicPhaseRealPhase_longActiveWindowTerm C₂ W₂ := by
  exact mul_le_mul hC hW hW₁_nonneg hC₂_nonneg

/-- Principal-strip terms are monotone in their two center counts at fixed
positive radius. -/
theorem logarithmicPhaseRealPhase_longPrincipalStripCrossingTerm_mono
    {C₁ C₂ P₁ P₂ eta : ℝ}
    (hC : C₁ ≤ C₂)
    (hP : P₁ ≤ P₂)
    (heta : 0 < eta) :
    Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingTerm C₁ P₁ eta ≤
      Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingTerm
        C₂ P₂ eta := by
  have hcount : C₁ + P₁ + 1 ≤ C₂ + P₂ + 1 :=
    add_le_add_right (add_le_add hC hP) 1
  have hfactor_nonneg : 0 ≤ 4 * (eta⁻¹ + 1) :=
    mul_nonneg zero_le_four
      (add_nonneg (inv_nonneg.mpr (le_of_lt heta)) zero_le_one)
  exact mul_le_mul_of_nonneg_right hcount hfactor_nonneg

/-- Complement-gap terms are monotone in their two center counts at fixed
positive radius. -/
theorem logarithmicPhaseRealPhase_longComplementGapTerm_mono
    {C₁ C₂ P₁ P₂ eta : ℝ}
    (hC : C₁ ≤ C₂)
    (hP : P₁ ≤ P₂)
    (heta : 0 < eta) :
    Real.logarithmicPhaseRealPhase_longComplementGapTerm C₁ P₁ eta ≤
      Real.logarithmicPhaseRealPhase_longComplementGapTerm C₂ P₂ eta := by
  have hcount : C₁ + P₁ + 1 ≤ C₂ + P₂ + 1 :=
    add_le_add_right (add_le_add hC hP) 1
  have hfactor_nonneg : 0 ≤ 4 * Real.pi * eta⁻¹ :=
    mul_nonneg
      (mul_nonneg zero_le_four Real.pi_nonneg)
      (inv_nonneg.mpr (le_of_lt heta))
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right hcount hfactor_nonneg) 1

/-- Sum of the canonical active resonance-window contributions. -/
def logarithmicPhaseRealPhase_longActiveWindowContribution
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    Real.logarithmicPhaseRealPhase_longActiveWindowTerm
      (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h)
      (Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h)

/-- Sum of the canonical principal-strip crossing contributions. -/
def logarithmicPhaseRealPhase_longPrincipalStripCrossingContribution
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingTerm
      (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h)
      (Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h)
      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)

/-- Sum of the canonical connected complement-gap contributions, including
the terminal sample of each shifted correlation. -/
def logarithmicPhaseRealPhase_longComplementGapContribution
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    Real.logarithmicPhaseRealPhase_longComplementGapTerm
      (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h)
      (Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h)
      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)

/-- Canonical refined additive budget for the positive long branch. -/
def logarithmicPhaseRealPhase_longRefinedAdditiveBudget
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  Real.logarithmicPhaseRealPhase_longActiveWindowContribution t a b +
    Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingContribution
      t a b +
    Real.logarithmicPhaseRealPhase_longComplementGapContribution t a b

/-- The canonical active-window contribution is nonnegative once the local
stationary-window budget is nonnegative on the Weyl shift range. -/
theorem logarithmicPhaseRealPhase_longActiveWindowContribution_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longActiveWindowContribution
      t a b := by
  exact
    Finset.sum_nonneg
      (fun h hh =>
        mul_nonneg
          (Real.logarithmicPhaseRealPhase_longResonanceCenterCount_nonneg
            t a b h)
          (Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
            t ht (b := b) h hh))

/-- The canonical principal-strip crossing contribution is nonnegative. -/
theorem logarithmicPhaseRealPhase_longPrincipalStripCrossingContribution_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingContribution
      t a b := by
  exact
    Finset.sum_nonneg
      (fun h hh =>
        have heta_pos :
            0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
          Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
            t ht h hh
        have hcount_nonneg :
            0 ≤
              Real.logarithmicPhaseRealPhase_longResonanceCenterCount
                  t a b h +
                Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                  t a b h + 1 :=
          add_nonneg
            (add_nonneg
              (Real.logarithmicPhaseRealPhase_longResonanceCenterCount_nonneg
                t a b h)
              (Real.logarithmicPhaseRealPhase_longPrincipalCenterCount_nonneg
                t a b h))
            zero_le_one
        have hgap_nonneg :
            0 ≤ 4 *
              ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1) :=
          mul_nonneg zero_le_four
            (add_nonneg (inv_nonneg.mpr (le_of_lt heta_pos)) zero_le_one)
        mul_nonneg hcount_nonneg hgap_nonneg)

/-- The canonical connected complement-gap contribution is nonnegative. -/
theorem logarithmicPhaseRealPhase_longComplementGapContribution_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longComplementGapContribution
      t a b := by
  exact
    Finset.sum_nonneg
      (fun h hh =>
        have heta_pos :
            0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
          Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
            t ht h hh
        have hcount_nonneg :
            0 ≤
              Real.logarithmicPhaseRealPhase_longResonanceCenterCount
                  t a b h +
                Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                  t a b h + 1 :=
          add_nonneg
            (add_nonneg
              (Real.logarithmicPhaseRealPhase_longResonanceCenterCount_nonneg
                t a b h)
              (Real.logarithmicPhaseRealPhase_longPrincipalCenterCount_nonneg
                t a b h))
            zero_le_one
        have hgap_nonneg :
            0 ≤ 4 * Real.pi *
              (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
          mul_nonneg
            (mul_nonneg zero_le_four Real.pi_nonneg)
            (inv_nonneg.mpr (le_of_lt heta_pos))
        add_nonneg (mul_nonneg hcount_nonneg hgap_nonneg) zero_le_one)

/-- The canonical refined additive budget is nonnegative. -/
theorem logarithmicPhaseRealPhase_longRefinedAdditiveBudget_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ) :
    0 ≤ Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b := by
  exact
    add_nonneg
      (add_nonneg
        (Real.logarithmicPhaseRealPhase_longActiveWindowContribution_nonneg
          t ht a b)
        (Real.logarithmicPhaseRealPhase_longPrincipalStripCrossingContribution_nonneg
          t ht a b))
      (Real.logarithmicPhaseRealPhase_longComplementGapContribution_nonneg
        t ht a b)

/-- For one Weyl shift, the older combined envelope term is exactly the sum
of the three refined analytic contributions. -/
theorem logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm_eq_refined
    (t : ℝ)
    (a b h : ℕ) :
    Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h =
      Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h *
          Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h +
        (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
            Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h +
            1) *
          (4 *
            ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1)) +
        ((Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
              Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h +
              1) *
            (4 * Real.pi *
              (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹) +
          1) := by
  let C : ℝ :=
    Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h
  let P : ℝ :=
    Real.logarithmicPhaseRealPhase_longPrincipalCenterCount t a b h
  let W : ℝ := Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h
  let U : ℝ :=
    4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1)
  let V : ℝ :=
    4 * Real.pi *
      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹
  have hcount :
      ((((Complex.realPhase_integerIncrementRangeActiveCenters
          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
          (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
        (Complex.realPhase_integerIncrementRangeActiveCenters
          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
          Real.pi).card + 1 : ℕ) : ℝ) = C + P + 1 := by
    exact
      Eq.trans
        (Nat.cast_add
          ((Complex.realPhase_integerIncrementRangeActiveCenters
            (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
            (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
          (Complex.realPhase_integerIncrementRangeActiveCenters
            (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
            (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
            Real.pi).card)
          1)
        (congrArg (fun value : ℝ => value + (1 : ℝ))
          (Nat.cast_add
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
              (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
              (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
              (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
              Real.pi).card))
  change C * W + _ * (U + V) + 1 = C * W + (C + P + 1) * U +
    ((C + P + 1) * V + 1)
  have hnormalized :
      C * W + (C + P + 1) * (U + V) + 1 =
        C * W + (C + P + 1) * U + ((C + P + 1) * V + 1) := by
    calc
      C * W + (C + P + 1) * (U + V) + 1 =
        C * W + ((C + P + 1) * U + (C + P + 1) * V) + 1 := by
        exact congrArg (fun value : ℝ => C * W + value + 1)
          (mul_add (C + P + 1) U V)
      _ = C * W + (C + P + 1) * U + ((C + P + 1) * V + 1) := by
        exact
          Eq.trans
            (congrArg (fun value : ℝ => value + 1)
              (add_assoc
                (C * W) ((C + P + 1) * U) ((C + P + 1) * V)).symm)
            (add_assoc
              (C * W + (C + P + 1) * U)
              ((C + P + 1) * V) 1)
  exact
    Eq.trans
      (congrArg
        (fun count : ℝ => C * W + count * (U + V) + 1)
        hcount)
      hnormalized

/-- The canonical combined additive envelope is exactly the refined additive
budget. -/
theorem logarithmicPhaseRealPhase_longAdditiveEnvelope_eq_refinedBudget
    (t : ℝ)
    (a b : ℕ) :
    Real.logarithmicPhaseRealPhase_longAdditiveEnvelope t a b =
      Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b := by
  let shifts := Complex.realPhase_secondDerivative_vdc_shiftRange
    (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
  have hterm :
      ∀ h ∈ shifts,
        Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h =
          Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h *
              Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h +
            (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
                Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                  t a b h + 1) *
              (4 *
                ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1)) +
            ((Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
                  Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                    t a b h + 1) *
                (4 * Real.pi *
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹) +
              1) :=
    fun h _hh =>
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm_eq_refined
        t a b h
  change (∑ h ∈ shifts,
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h) = _
  calc
    (∑ h ∈ shifts,
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h) =
        ∑ h ∈ shifts,
          (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h *
              Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h +
            (Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
                Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                  t a b h + 1) *
              (4 *
                ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1)) +
            ((Real.logarithmicPhaseRealPhase_longResonanceCenterCount t a b h +
                  Real.logarithmicPhaseRealPhase_longPrincipalCenterCount
                    t a b h + 1) *
                (4 * Real.pi *
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹) + 1)) :=
      Finset.sum_congr rfl hterm
    _ = Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b := by
      exact
        Eq.trans
          (Finset.sum_add_distrib)
          (congrArg
            (fun value : ℝ =>
              value +
                Real.logarithmicPhaseRealPhase_longComplementGapContribution
                  t a b)
            Finset.sum_add_distrib)

/-- The capped canonical contribution for one Weyl shift.  It records the
pointwise minimum between the all-integer resonance decomposition and the
trivial cardinality bound for the same shifted correlation. -/
abbrev logarithmicPhaseRealPhase_longCappedEnvelopeTerm
    (t : ℝ)
    (a b h : ℕ) : ℝ :=
  min
    (Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h)
    (((Finset.Icc a (b - h)).card : ℝ))

/-- Canonical shifted-correlation envelope with the all-integer resonance
majorant capped by the trivial shifted-block cardinality on each Weyl shift. -/
abbrev logarithmicPhaseRealPhase_longCappedEnvelope
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h

/-- The capped envelope term is bounded by the all-integer resonance
decomposition term. -/
theorem logarithmicPhaseRealPhase_longCappedEnvelopeTerm_le_additive
    (t : ℝ)
    (a b h : ℕ) :
    Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h ≤
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h := by
  exact
    min_le_left
      (Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h)
      (((Finset.Icc a (b - h)).card : ℝ))

/-- The capped envelope term is bounded by the trivial shifted block
cardinality. -/
theorem logarithmicPhaseRealPhase_longCappedEnvelopeTerm_le_card
    (t : ℝ)
    (a b h : ℕ) :
    Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h ≤
      (((Finset.Icc a (b - h)).card : ℝ)) := by
  exact
    min_le_right
      (Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h)
      (((Finset.Icc a (b - h)).card : ℝ))

/-- The capped envelope term is nonnegative when both cap inputs are
nonnegative. -/
theorem logarithmicPhaseRealPhase_longCappedEnvelopeTerm_nonneg
    (t : ℝ)
    (a b h : ℕ)
    (hadd :
      0 ≤ Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h) :
    0 ≤ Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h := by
  exact le_min hadd (Nat.cast_nonneg (Finset.Icc a (b - h)).card)

/-- Canonical Weyl radicand for the additive all-integer monotone-curvature
decomposition. -/
abbrev logarithmicPhaseRealPhase_longAdditiveRadicand
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ((Real.secondDerivativeVdc_blockLength a b) +
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
    (((Real.secondDerivativeVdc_blockLength a b) +
        2 * Real.logarithmicPhaseRealPhase_longAdditiveEnvelope t a b) *
      (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹))

/-- Canonical Weyl radicand expressed using the refined three-component
additive budget. -/
def logarithmicPhaseRealPhase_longRefinedAdditiveRadicand
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ((Real.secondDerivativeVdc_blockLength a b) +
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
    (((Real.secondDerivativeVdc_blockLength a b) +
        2 *
          Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b) *
      (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹))

/-- The legacy canonical additive radicand and the refined-budget radicand
are exactly equal. -/
theorem logarithmicPhaseRealPhase_longAdditiveRadicand_eq_refined
    (t : ℝ)
    (a b : ℕ) :
    Real.logarithmicPhaseRealPhase_longAdditiveRadicand t a b =
      Real.logarithmicPhaseRealPhase_longRefinedAdditiveRadicand t a b := by
  exact
    congrArg
      (fun budget : ℝ =>
        ((Real.secondDerivativeVdc_blockLength a b) +
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) + 2 * budget) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)))
      (Real.logarithmicPhaseRealPhase_longAdditiveEnvelope_eq_refinedBudget
        t a b)

/-- Canonical block-length bound by the successor right endpoint. -/
theorem logarithmicPhaseRealPhase_long_blockLength_le_rightEndpoint
    {a b : ℕ}
    (hab : a ≤ b) :
    Real.secondDerivativeVdc_blockLength a b ≤ ((b + 1 : ℕ) : ℝ) := by
  have hab_succ : a ≤ b + 1 :=
    le_trans hab (Nat.le_succ b)
  have hlength :
      Real.secondDerivativeVdc_blockLength a b =
        ((b + 1 : ℕ) : ℝ) - (a : ℝ) :=
    Real.secondDerivativeVdc_blockLength_eq_endpoint_length hab_succ
  have hsub :
      ((b + 1 : ℕ) : ℝ) - (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
    sub_le_self ((b + 1 : ℕ) : ℝ) (Nat.cast_nonneg a)
  exact
    Eq.subst
      (motive := fun length : ℝ => length ≤ ((b + 1 : ℕ) : ℝ))
      hlength.symm
      hsub

/-- Canonical Weyl shift-length bound at the square-root transition scale. -/
theorem logarithmicPhaseRealPhase_long_shiftLength_le_sqrt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ) ≤
      Real.sqrt (1 + ‖t‖) := by
  exact Real.secondDerivativeVdc_weylShiftLength_le_sqrt ht

/-- The first Weyl radicand factor is bounded by the successor right endpoint
plus the canonical square-root scale. -/
theorem logarithmicPhaseRealPhase_long_blockLength_add_shiftLength_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b) :
    Real.secondDerivativeVdc_blockLength a b +
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) + Real.sqrt (1 + ‖t‖) := by
  exact
    add_le_add
      (Real.logarithmicPhaseRealPhase_long_blockLength_le_rightEndpoint hab)
      (Real.logarithmicPhaseRealPhase_long_shiftLength_le_sqrt t ht)

/-- The canonical refined radicand retains the diagonal `A²/H` lower bound. -/
theorem logarithmicPhaseRealPhase_long_blockLength_sq_mul_shiftInv_le_refinedRadicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ) :
    (Real.secondDerivativeVdc_blockLength a b) ^ 2 *
        ((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)⁻¹) ≤
      Real.logarithmicPhaseRealPhase_longRefinedAdditiveRadicand t a b := by
  have hA : 0 ≤ Real.secondDerivativeVdc_blockLength a b :=
    Real.secondDerivativeVdc_blockLength_nonneg a b
  have hH :
      0 < (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) :=
    Nat.cast_pos.mpr
      (Real.secondDerivativeVdc_weylShiftLength_pos ht)
  have hE :
      0 ≤ Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b :=
    Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget_nonneg
      t ht a b
  exact Real.secondDerivativeVdc_sq_mul_inv_le_radicand hA hH hE

/-- Final product arithmetic for the refined canonical radicand.  The two
remaining inputs are precisely the first-factor and budget-factor estimates
owned by the preceding arithmetic lemmas. -/
theorem logarithmicPhaseRealPhase_longRefinedAdditiveRadicand_le_target_sq_of_factor_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (a b : ℕ)
    (hfirst :
      Real.secondDerivativeVdc_blockLength a b +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))))
    (hsecond :
      Real.secondDerivativeVdc_blockLength a b +
          2 * Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget
            t a b ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) *
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) :
    Real.logarithmicPhaseRealPhase_longRefinedAdditiveRadicand t a b ≤
      (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)))) ^ 2 := by
  let A : ℝ := Real.secondDerivativeVdc_blockLength a b
  let H : ℝ := (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)
  let E : ℝ :=
    Real.logarithmicPhaseRealPhase_longRefinedAdditiveBudget t a b
  let M : ℝ :=
    80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))
  have hA_nonneg : 0 ≤ A := by
    exact Real.secondDerivativeVdc_blockLength_nonneg a b
  have hH_pos : 0 < H := by
    exact Nat.cast_pos.mpr
      (Real.secondDerivativeVdc_weylShiftLength_pos ht)
  have hquotient_nonneg :
      0 ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    div_nonneg (Nat.cast_nonneg (b + 1)) (norm_nonneg t)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hM_nonneg : 0 ≤ M := by
    exact mul_nonneg (Nat.cast_nonneg 80)
      (add_nonneg hquotient_nonneg hsqrt_nonneg)
  exact
    Real.secondDerivativeVdc_radicand_le_sq_of_factor_bounds
      hA_nonneg hH_pos hM_nonneg hfirst hsecond

/-- Canonical capped Weyl radicand for the additive all-integer
monotone-curvature decomposition. -/
abbrev logarithmicPhaseRealPhase_longCappedRadicand
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ((Real.secondDerivativeVdc_blockLength a b) +
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
    (((Real.secondDerivativeVdc_blockLength a b) +
        2 * Real.logarithmicPhaseRealPhase_longCappedEnvelope t a b) *
      (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹))

/-- The capped shifted-correlation envelope is bounded by the additive
all-integer resonance envelope. -/
theorem logarithmicPhaseRealPhase_longCappedEnvelope_le_additiveEnvelope
    (t : ℝ)
    (a b : ℕ) :
    Real.logarithmicPhaseRealPhase_longCappedEnvelope t a b ≤
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelope t a b := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
      Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h
  exact Finset.sum_le_sum
    (fun h _hh =>
      Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm_le_additive
        t a b h)

/-- The capped Weyl radicand is bounded by the uncapped additive all-integer
resonance radicand. -/
theorem logarithmicPhaseRealPhase_longCappedRadicand_le_additiveRadicand
    (t : ℝ)
    (a b : ℕ) :
    Real.logarithmicPhaseRealPhase_longCappedRadicand t a b ≤
      Real.logarithmicPhaseRealPhase_longAdditiveRadicand t a b := by
  let B : ℝ := Real.secondDerivativeVdc_blockLength a b
  let H : ℝ := (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)
  let C : ℝ := Real.logarithmicPhaseRealPhase_longCappedEnvelope t a b
  let A : ℝ := Real.logarithmicPhaseRealPhase_longAdditiveEnvelope t a b
  have hC_le_A : C ≤ A := by
    unfold C A
    exact
      Real.logarithmicPhaseRealPhase_longCappedEnvelope_le_additiveEnvelope
        t a b
  have htwoC_le_twoA : 2 * C ≤ 2 * A :=
    mul_le_mul_of_nonneg_left hC_le_A zero_le_two
  have hinner :
      B + 2 * C ≤ B + 2 * A :=
    add_le_add_left htwoC_le_twoA B
  have hH_inv_nonneg : 0 ≤ H⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖))
  have hmiddle :
      (B + 2 * C) * H⁻¹ ≤ (B + 2 * A) * H⁻¹ :=
    mul_le_mul_of_nonneg_right hinner hH_inv_nonneg
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact Real.secondDerivativeVdc_blockLength_nonneg a b
  have hH_nonneg : 0 ≤ H := by
    unfold H
    exact Nat.cast_nonneg (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
  have hfactor_nonneg : 0 ≤ B + H :=
    add_nonneg hB_nonneg hH_nonneg
  have hrad :
      (B + H) * ((B + 2 * C) * H⁻¹) ≤
        (B + H) * ((B + 2 * A) * H⁻¹) :=
    mul_le_mul_of_nonneg_left hmiddle hfactor_nonneg
  exact hrad

end Real

end

end LFunctions
end Boundary
