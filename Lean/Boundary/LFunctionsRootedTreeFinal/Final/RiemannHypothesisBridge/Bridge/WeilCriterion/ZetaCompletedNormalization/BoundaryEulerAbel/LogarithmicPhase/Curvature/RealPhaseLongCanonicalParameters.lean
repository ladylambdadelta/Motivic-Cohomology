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

/-- Weighted additive all-integer shifted-correlation mass for the exact
second-derivative Weyl inequality. -/
abbrev logarithmicPhaseRealPhase_longWeightedAdditiveMass
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
    (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
      Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h

/-- Weighted Weyl radicand for the additive all-integer monotone-curvature
decomposition. -/
abbrev logarithmicPhaseRealPhase_longWeightedAdditiveRadicand
    (t : ℝ)
    (a b : ℕ) : ℝ :=
  ((Real.secondDerivativeVdc_blockLength a b) +
      (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
    (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
        Real.secondDerivativeVdc_blockLength a b +
        2 * Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b) *
      (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))⁻¹))

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

/-- For a single envelope term on one Weyl shift, the contribution is bounded
by a constant multiple of the envelope term size. On a long block, this is
controlled by the resonance-center cardinality and gap majorant. -/
theorem logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm_bounded_on_longBlock
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hh :
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖))
    (hW_nonneg :
      0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h) :
    Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h ≤
      100 * ((b - a : ℕ) : ℝ) * Real.pi⁻¹ + 100 := by
  sorry

end Real

end

end LFunctions
end Boundary
