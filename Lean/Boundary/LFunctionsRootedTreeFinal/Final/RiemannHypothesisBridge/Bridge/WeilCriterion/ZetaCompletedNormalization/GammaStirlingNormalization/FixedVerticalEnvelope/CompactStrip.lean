import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.VerticalStrip

/-!
# Fixed vertical compact strip bounds

This subowner contains the compact-strip Gamma and reciprocal Gamma bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def Complex.fixedRealPartVerticalCompactHeightSet
    (H : ℝ) : Set ℝ :=
  {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖ ∧ ‖b‖ ≤ H}

/-- Closed real strip with compact vertical-height window.

This is the two-dimensional compact-height owner domain needed for uniform
Gamma and Gamma-ratio bounds when the real part varies in a closed interval. -/
def Complex.closedRealStripCompactHeightSet
    (A B L H : ℝ) : Set ℂ :=
  {z : ℂ | A ≤ z.re} ∩ {z : ℂ | z.re ≤ B} ∩
    {z : ℂ | L ≤ ‖z.im‖} ∩ {z : ℂ | ‖z.im‖ ≤ H}

/-- The closed real-strip compact-height set is closed. -/
theorem Complex.closedRealStripCompactHeightSet_isClosed
    (A B L H : ℝ) :
    IsClosed (Complex.closedRealStripCompactHeightSet A B L H) := by
  have hleft : IsClosed {z : ℂ | A ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ B} :=
    isClosed_le Complex.continuous_re continuous_const
  have him_lower : IsClosed {z : ℂ | L ≤ ‖z.im‖} :=
    isClosed_le continuous_const (Complex.continuous_im.norm)
  have him_upper : IsClosed {z : ℂ | ‖z.im‖ ≤ H} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  exact ((hleft.inter hright).inter him_lower).inter him_upper

/-- The closed real-strip compact-height set is bounded. -/
theorem Complex.closedRealStripCompactHeightSet_isBounded
    (A B L H : ℝ) :
    Bornology.IsBounded (Complex.closedRealStripCompactHeightSet A B L H) := by
  exact
    isBounded_iff_forall_norm_le.2
      ⟨|A| + |B| + H + 1,
        fun z hz =>
          have hz_left : A ≤ z.re := hz.1.1.1
          have hz_right : z.re ≤ B := hz.1.1.2
          have hz_im_upper : ‖z.im‖ ≤ H := hz.2
          have hre_abs_le : |z.re| ≤ |A| + |B| := by
            have hleft_bound : -(|A| + |B|) ≤ z.re := by
              have hneg_sum : -(|A| + |B|) = -|A| + -|B| :=
                neg_add |A| |B|
              have hneg_sum_le : -|A| + -|B| ≤ -|A| := by
                have hb_nonpos : -|B| ≤ 0 :=
                  neg_nonpos.mpr (abs_nonneg B)
                exact
                  le_trans
                    (add_le_add_left hb_nonpos (-|A|))
                    (le_of_eq (add_zero (-|A|)))
              have hneg_abs_A_le_A : -|A| ≤ A :=
                neg_abs_le A
              exact
                le_trans
                  (le_of_eq hneg_sum)
                  (le_trans hneg_sum_le (le_trans hneg_abs_A_le_A hz_left))
            have hright_bound : z.re ≤ |A| + |B| := by
              have hB_le_abs_B : B ≤ |B| :=
                le_abs_self B
              have h_abs_B_le_sum : |B| ≤ |A| + |B| :=
                le_add_of_nonneg_left (abs_nonneg A)
              exact le_trans hz_right (le_trans hB_le_abs_B h_abs_B_le_sum)
            exact abs_le.mpr ⟨hleft_bound, hright_bound⟩
          have him_abs_le : |z.im| ≤ H := by
            exact
              Eq.subst
                (motive := fun x : ℝ => x ≤ H)
                (Real.norm_eq_abs z.im)
                hz_im_upper
          have hnorm_le_coord : ‖z‖ ≤ |z.re| + |z.im| :=
            Eq.subst
              (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
              (Complex.norm_eq_abs z).symm
              (Complex.abs_le_abs_re_add_abs_im z)
          have hcoord_le : |z.re| + |z.im| ≤ (|A| + |B|) + H :=
            add_le_add hre_abs_le him_abs_le
          have htarget : (|A| + |B|) + H ≤ |A| + |B| + H + 1 :=
            le_add_of_nonneg_right zero_le_one
          le_trans hnorm_le_coord (le_trans hcoord_le htarget)⟩

/-- The closed real-strip compact-height set is compact. -/
theorem Complex.closedRealStripCompactHeightSet_isCompact
    (A B L H : ℝ) :
    IsCompact (Complex.closedRealStripCompactHeightSet A B L H) :=
  Metric.isCompact_of_isClosed_isBounded
    (Complex.closedRealStripCompactHeightSet_isClosed A B L H)
    (Complex.closedRealStripCompactHeightSet_isBounded A B L H)

/-- `Complex.Gamma` has no zeros on a closed real strip whose imaginary
coordinate is bounded away from zero. -/
theorem Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L)
    {w : ℂ}
    (hw : w ∈ Complex.closedRealStripCompactHeightSet A B L H) :
    Complex.Gamma w ≠ 0 :=
  fun hzero =>
    match (Complex.Gamma_eq_zero_iff w).mp hzero with
    | ⟨n, hn⟩ =>
        have him_eq : w.im = (-(n : ℂ)).im :=
          congrArg Complex.im hn
        have hright_im : (-(n : ℂ)).im = 0 := by
          calc
            (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
            _ = 0 := neg_zero
        have hw_im_zero : w.im = 0 :=
          Eq.trans him_eq hright_im
        have hnorm_zero : ‖w.im‖ = 0 := by
          calc
            ‖w.im‖ = ‖(0 : ℝ)‖ := congrArg norm hw_im_zero
            _ = 0 := norm_zero
        have hL_le_zero : L ≤ 0 := by
          calc
            L ≤ ‖w.im‖ := hw.1.2
            _ = 0 := hnorm_zero
        (not_lt_of_ge hL_le_zero) hL_pos

/-- `Complex.Gamma` is continuous on a closed real strip whose imaginary
coordinate is bounded away from zero. -/
theorem Complex.continuousOn_Gamma_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ContinuousOn
      Complex.Gamma
      (Complex.closedRealStripCompactHeightSet A B L H) :=
  fun w hw =>
    have hgamma_ne : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet A B L H hL_pos hw
    have hpole_free : ∀ n : ℕ, w ≠ -n :=
      fun n hn =>
        hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨n, hn⟩)
    (Complex.differentiableAt_Gamma w hpole_free).continuousAt.continuousWithinAt

/-- Compact-height closed-rectangle bound for the Gamma norm. -/
theorem Complex.Gamma_closedRealStripCompactHeightSet_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRealStripCompactHeightSet A B L H →
          ‖Complex.Gamma w‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.closedRealStripCompactHeightSet_isCompact A B L H)
      (Complex.continuousOn_Gamma_closedRealStripCompactHeightSet
        A B L H hL_pos) with
  | ⟨M, hM⟩ =>
      let C : ℝ := max 1 M
      have hC_pos : 0 < C :=
        lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
      exact
        ⟨C, hC_pos,
          fun w hw =>
            calc
              ‖Complex.Gamma w‖ ≤ M := hM w hw
              _ ≤ C := le_max_right 1 M⟩

/-- Pointwise form of the compact-height closed-rectangle Gamma bound. -/
theorem Complex.Gamma_closedRealStrip_compactHeight_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        L ≤ ‖w.im‖ →
        ‖w.im‖ ≤ H →
          ‖Complex.Gamma w‖ ≤ C := by
  match Complex.Gamma_closedRealStripCompactHeightSet_bound A B L H hL_pos with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_left hw_right hw_lower hw_upper =>
            hC w ⟨⟨⟨hw_left, hw_right⟩, hw_lower⟩, hw_upper⟩⟩

/-- The reciprocal Gamma function is continuous on a closed real-strip
compact-height rectangle whose imaginary coordinate is bounded away from zero. -/
theorem Complex.continuousOn_Gamma_inv_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ContinuousOn
      (fun w : ℂ => (Complex.Gamma w)⁻¹)
      (Complex.closedRealStripCompactHeightSet A B L H) :=
  fun w hw =>
    have hgamma_ne : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet A B L H hL_pos hw
    have hpole_free : ∀ n : ℕ, w ≠ -n :=
      fun n hn =>
        hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨n, hn⟩)
    have hgamma_cont : ContinuousAt Complex.Gamma w :=
      (Complex.differentiableAt_Gamma w hpole_free).continuousAt
    (hgamma_cont.inv₀ hgamma_ne).continuousWithinAt

/-- Compact-height closed-rectangle bound for the reciprocal Gamma norm. -/
theorem Complex.Gamma_inv_closedRealStripCompactHeightSet_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRealStripCompactHeightSet A B L H →
          ‖(Complex.Gamma w)⁻¹‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.closedRealStripCompactHeightSet_isCompact A B L H)
      (Complex.continuousOn_Gamma_inv_closedRealStripCompactHeightSet
        A B L H hL_pos) with
  | ⟨M, hM⟩ =>
      let C : ℝ := max 1 M
      have hC_pos : 0 < C :=
        lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
      exact
        ⟨C, hC_pos,
          fun w hw =>
            calc
              ‖(Complex.Gamma w)⁻¹‖ ≤ M := hM w hw
              _ ≤ C := le_max_right 1 M⟩

/-- A compact-height logarithmic-derivative bound.  The height cutoff keeps
the Gamma pole locus outside the owner domain; complex analyticity then
supplies continuity of the derivative before compactness is applied. -/
theorem Complex.Gamma_logDerivative_closedRealStripCompactHeightSet_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRealStripCompactHeightSet A B L H →
          ‖deriv Complex.Gamma w / Complex.Gamma w‖ ≤ C := by
  let U : Set ℂ := {w : ℂ | 0 < ‖w.im‖}
  have hU_open : IsOpen U := by
    exact isOpen_lt continuous_const (Complex.continuous_im.norm)
  have hGamma_diff : DifferentiableOn ℂ Complex.Gamma U := by
    intro w hw
    apply Complex.differentiableAt_Gamma
    intro n hn
    intro hEq
    have hImEq : w.im = (-(n : ℂ)).im :=
      congrArg Complex.im hEq
    have hPoleIm : (-(n : ℂ)).im = 0 := by
      calc
        (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
        _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
        _ = 0 := neg_zero
    have hImZero : w.im = 0 := hImEq.trans hPoleIm
    have hNormZero : ‖w.im‖ = 0 := congrArg norm hImZero
    exact (not_lt_of_ge (le_of_eq hNormZero.symm)) hw
  have hGamma_cont : ContinuousOn Complex.Gamma U :=
    hGamma_diff.continuousOn
  have hGamma_deriv_cont :
      ContinuousOn (deriv Complex.Gamma) U := by
    exact
      (hGamma_diff.contDiffOn hU_open).continuousOn_deriv_of_isOpen
        hU_open (by exact le_top)
  have hquot_cont :
      ContinuousOn (fun w : ℂ => deriv Complex.Gamma w / Complex.Gamma w) U := by
    exact hGamma_deriv_cont.div hGamma_cont
  have hK_compact :
      IsCompact (Complex.closedRealStripCompactHeightSet A B L H) :=
    Complex.closedRealStripCompactHeightSet_isCompact A B L H
  have hK_sub :
      Complex.closedRealStripCompactHeightSet A B L H ⊆ U := by
    intro w hw
    have hL_le_norm : L ≤ ‖w.im‖ := hw.1.2.1
    exact lt_of_lt_of_le hL_pos hL_le_norm
  have hK_bound :=
    IsCompact.exists_bound_of_continuousOn hK_compact
      (hquot_cont.mono hK_sub)
  match hK_bound with
  | ⟨M, hM⟩ =>
      let C : ℝ := max 1 M
      have hC_pos : 0 < C :=
        lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
      exact ⟨C, hC_pos, fun w hw =>
        (hM w hw).trans (le_max_right 1 M)⟩

/- Pointwise form of the compact-height closed-rectangle reciprocal Gamma bound. -/
theorem Complex.Gamma_inv_closedRealStrip_compactHeight_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        L ≤ ‖w.im‖ →
        ‖w.im‖ ≤ H →
          ‖(Complex.Gamma w)⁻¹‖ ≤ C := by
  match Complex.Gamma_inv_closedRealStripCompactHeightSet_bound A B L H hL_pos with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_left hw_right hw_lower hw_upper =>
            hC w ⟨⟨⟨hw_left, hw_right⟩, hw_lower⟩, hw_upper⟩⟩

end
end LFunctions
end Boundary
