import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PhaseDefs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUnconditionalLong
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDyadicCurvature

/-!
# Logarithmic phase curvature owner

This file owns the small transport layer from the real scalar logarithmic phase
to the concrete complex samples `n ^ (-it)`.  The analytic packet estimate for
the real phase is a separate upstream theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-! The unconditional long branch uses the finite resonance-family complement,
not a global resonance-avoidance assertion. -/

theorem Complex.logarithmicPhaseRealPhase_resonanceComplement_cover
    (t : ℝ)
    {a b : ℕ}
    (lam : ℝ)
    (K : Finset ℤ)
    (hab : a ≤ b)
    (hlam : lam ≤ Real.pi)
    (hwindow :
      ∀ k : ℤ,
        k ∈ K →
          ∃ c d : ℕ,
            Complex.realPhase_integerIncrementResonanceWindow
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                a b (2 * Real.pi * (k : ℝ)) lam =
              Finset.Ico c d) :
    ∃ gaps : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion gaps =
          Complex.realPhase_integerResonanceFamilyComplement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b lam K ∧
        (∀ p₁ : ℕ × ℕ,
          p₁ ∈ gaps →
            ∀ p₂ : ℕ × ℕ,
              p₂ ∈ gaps →
                p₁ ≠ p₂ →
                  Disjoint (Finset.Ico p₁.1 p₁.2)
                    (Finset.Ico p₂.1 p₂.2)) ∧
        Complex.realPhase_IcoFamilyIntervalConnected gaps ∧
        Complex.realPhase_IcoFamilyBounded a b gaps ∧
        gaps.card ≤ K.card + 1 := by
  exact
    Complex.exists_bounded_IcoFamily_connected_cover_resonanceFamilyComplement_of_window_eq_of_le_pi
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b lam K hab hlam hwindow

/-- Every canonical Weyl shift is positive, in the quantified shape required
by the range-counted active-center owner theorem. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_pos
    (t : ℝ) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        1 ≤ h := by
  intro h hh
  exact Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh

/-- The canonical shifted-curvature lower parameter is positive on every
Weyl shift in the positive long branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 <
          ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ) := by
  intro h hh
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_pos
      (t := t) (b := b) (h := h) ht
      (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)

/-- The square-root resonance thickness attached to the canonical shifted
curvature parameter is positive on every Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_sqrt_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 <
          Real.sqrt
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)) := by
  intro h hh
  exact
    Real.sqrt_pos.mpr
      (Complex.logarithmicPhaseRealPhase_shiftRange_lowerParameter_pos
        (t := t) (b := b) ht h hh)

/-- The canonical shifted-curvature lower parameter is nonnegative on every
Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_lowerParameter_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ} :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        0 ≤
          ‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ) := by
  intro h hh
  exact
    le_of_lt
      (Complex.logarithmicPhaseRealPhase_shiftRange_lowerParameter_pos
        (t := t) (b := b) ht h hh)

/-- If the canonical shifted-curvature lower parameter is at most `π`, then
the square-root resonance thickness is also at most `π`. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_sqrt_lowerParameter_le_pi
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b : ℕ}
    (hlam_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤ Real.pi) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Real.sqrt
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) ≤ Real.pi := by
  intro h hh
  let lam : ℝ :=
    ‖t‖ *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹) *
      (h : ℝ)
  have hpi_nonneg : 0 ≤ Real.pi :=
    Real.pi_pos.le
  have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
    le_trans Real.one_le_pi_div_two
      (half_le_self Real.pi_pos.le)
  have hpi_le_pisq : Real.pi ≤ Real.pi ^ 2 := by
    have hpi_mul_le : Real.pi ≤ Real.pi * Real.pi :=
      le_mul_of_one_le_right Real.pi_pos.le hone_le_pi
    exact
      Eq.subst
        (motive := fun right : ℝ => Real.pi ≤ right)
        (pow_two Real.pi).symm
        hpi_mul_le
  have hlam_le_pisq : lam ≤ Real.pi ^ 2 :=
    le_trans (hlam_pi h hh) hpi_le_pisq
  exact
    Real.sqrt_le_iff.mpr
      (And.intro hpi_nonneg hlam_le_pisq)

/-- Shifted logarithmic derivative norms are antitone on every canonical Weyl
shift interval in the positive long branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_deriv_norm_antitone_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        AntitoneOn
          (fun x : ℝ =>
            ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h) x‖)
          (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) := by
  exact
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt

/-- Shifted logarithmic derivative norms have the canonical curvature lower
scale on every canonical Weyl shift interval in the positive long branch. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_deriv_norm_lower_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ x : ℝ,
          x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
            ‖t‖ *
                ((((b + 1 : ℕ) : ℝ) *
                  (((b + 1 : ℕ) : ℝ)))⁻¹) *
                (h : ℝ) ≤
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖ := by
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  intro h hh x hx
  have hh_gap : h ≤ b - a :=
    le_trans
      (Complex.realPhase_secondDerivative_vdc_shiftRange_le hh)
      hgap
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc_of_nonneg
      t ht ht_nonneg ha hab hh_gap hx

/-- Raw shifted-increment monotonicity is automatic in the positive
logarithmic long branch, in the quantified shape required by the Weyl-envelope
owner theorem. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_integerIncrementMonotone_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Complex.realPhase_integerIncrementMonotoneOn
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) := by
  intro h _hh
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
      t ht_nonneg ha

/-- Once the shifted increments are known to remain on the principal branch,
raw positive-branch monotonicity transports to reduced-increment monotonicity
for every canonical Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_reducedIntegerIncrementMonotone_of_gap_pi
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hgap_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Complex.realPhase_integerIncrement
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                n ≤ Real.pi) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        Complex.realPhase_reducedIntegerIncrementMonotoneOn
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_reduced_mono_of_gap_pi
      t ht_nonneg ha hgap_pi

/-- A positive integer logarithmic-phase sample is the corresponding
real-phase exponential sample. -/
theorem Complex.logarithmicPhase_integer_sample_eq_realPhase_exp
    (t : ℝ)
    {n : ℕ}
    (hn_one : 1 ≤ n) :
    ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ)) := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hsample_function :
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n :=
    (Complex.logarithmicPhase_integer_sample_eq t hn_pos).symm
  have hfunction_phase :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n =
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
      t n
  exact Eq.trans hsample_function hfunction_phase

/-- A positive integer block of logarithmic-phase samples is the corresponding
real-phase exponential block. -/
theorem Complex.logarithmicPhase_integer_block_eq_realPhase_exp_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    (∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t n : ℂ)) := by
  exact Finset.sum_congr
    (Eq.refl (Finset.Icc a b))
    (fun n hn_mem =>
      have hn_one : 1 ≤ n :=
        le_trans ha (Finset.mem_Icc.mp hn_mem).1
      Complex.logarithmicPhase_integer_sample_eq_realPhase_exp
        (t := t)
        (n := n)
        hn_one)

/-- Transport a real-phase curvature block estimate to the concrete logarithmic
samples. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hreal :
      (‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖) ≤
        80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :
    (‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖) ≤
      80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) := by
  have hsample :
      (∑ n ∈ Finset.Icc a b,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) :=
    Complex.logarithmicPhase_integer_block_eq_realPhase_exp_block
      (t := t)
      (a := a)
      (b := b)
      (ha := ha)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 * (((b + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)))
      hsample.symm
      hreal

/-- Logarithmic curvature block estimate for the concrete samples `n ^ (-it)`
from an explicit long-branch owner bound. -/
/-! The witness-free owner bridge.  The real-phase estimate comes from the
canonical packet endpoint; this theorem performs only the already-proved
transport to the concrete complex samples. -/
theorem Complex.logarithmicPhase_curvature_integer_block_bound_unconditional_geometry
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖) +
        Real.sqrt (1 + ‖t‖)) := by
  have hreal :=
    Complex.logarithmicPhaseRealPhase_long_nonneg_unconditional
      t ht_nonneg ht a b hgeometry
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound_of_realPhase
      t (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry) hreal

end

end LFunctions
end Boundary
