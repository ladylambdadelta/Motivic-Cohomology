import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.ReciprocalHalfStrip

/-!
# Fixed vertical Gamma envelope bounds

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi


/-- Upper ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaUpperRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- Lower ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaLowerRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- The fixed vertical-line point depends continuously on the height. -/
theorem Complex.continuousAt_fixedRealPartVerticalPoint_height
    (a b : ℝ) :
    ContinuousAt (fun x : ℝ => Complex.fixedRealPartVerticalPoint a x) b := by
  exact continuousAt_const.add
    (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)

/-- The fixed vertical-line Stirling envelope depends continuously on height. -/
theorem Complex.continuousAt_fixedRealPartVerticalStirlingEnvelope_height
    (a b : ℝ) :
    ContinuousAt
      (fun x : ℝ => Complex.fixedRealPartVerticalStirlingEnvelope a x) b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have hexp_arg_cont :
      ContinuousAt (fun x : ℝ => (-(Real.pi / 2)) * ‖x‖) b :=
    continuousAt_const.mul continuousAt_id.norm
  have hpow_base_cont :
      ContinuousAt (fun x : ℝ => 1 + ‖x‖) b :=
    continuousAt_const.add continuousAt_id.norm
  exact
    hexp_arg_cont.rexp.mul
      (hpow_base_cont.rpow_const (Or.inl hbase_pos.ne'))

/-- The fixed-line compact-height set is compact. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_isCompact
    (H : ℝ) :
    IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  have hclosed_inner : IsClosed {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖} :=
    isClosed_Ici.preimage continuous_norm
  have hclosed_outer : IsClosed {b : ℝ | ‖b‖ ≤ H} :=
    isClosed_Iic.preimage continuous_norm
  have hclosed :
      IsClosed (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    hclosed_inner.inter hclosed_outer
  have hsubset :
      Complex.fixedRealPartVerticalCompactHeightSet H ⊆ Set.Icc (-H) H := by
    exact
      fun b hb =>
        have hb_abs_le : |b| ≤ H := by
          calc
            |b| = ‖b‖ := (Real.norm_eq_abs b).symm
            _ ≤ H := hb.2
        abs_le.mp hb_abs_le
  exact isCompact_Icc.of_isClosed_subset hclosed hsubset

/-- The fixed-line compact-height set is nonempty once `H ≥ 1 / 2`. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_nonempty
    {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H) :
    (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty := by
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 :=
    le_of_lt (half_pos zero_lt_one)
  have hnorm_half : ‖(1 / 2 : ℝ)‖ = 1 / 2 :=
    Real.norm_of_nonneg hhalf_nonneg
  exact
    ⟨(1 / 2 : ℝ),
      And.intro
      (le_of_eq hnorm_half.symm)
      (calc
        ‖(1 / 2 : ℝ)‖ = 1 / 2 := hnorm_half
        _ ≤ H := hH)⟩

/-- `Gamma` is nonzero on the fixed-line compact-height strip. -/
theorem Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight
    {a H b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 := by
  exact
    fun hzero =>
      match (Complex.Gamma_eq_zero_iff
          (Complex.fixedRealPartVerticalPoint a b)).mp hzero with
      | ⟨n, hn⟩ =>
        have him_eq :
            (Complex.fixedRealPartVerticalPoint a b).im = (-(n : ℂ)).im :=
          congrArg Complex.im hn
        have hleft_im :
            (Complex.fixedRealPartVerticalPoint a b).im = b :=
          Complex.fixedRealPartVerticalPoint_im a b
        have hright_im : (-(n : ℂ)).im = 0 := by
          calc
            (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.natCast_im n)
            _ = 0 := neg_zero
        have hb_zero : b = 0 :=
          Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
        have hnorm_zero : ‖b‖ = 0 :=
          Eq.trans (congrArg norm hb_zero) (norm_zero : ‖(0 : ℝ)‖ = 0)
        have hhalf_pos : (0 : ℝ) < 1 / 2 :=
          half_pos zero_lt_one
        have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
          not_le.mpr hhalf_pos
        have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 := by
          calc
            (1 / 2 : ℝ) ≤ ‖b‖ := hb.1
            _ = 0 := hnorm_zero
        hnot hhalf_le_zero

/-- The fixed-line Gamma ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ =>
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  exact
    fun b hb =>
      have hgamma_ne :
          Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
        Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
      have hpole_free :
          ∀ n : ℕ, Complex.fixedRealPartVerticalPoint a b ≠ -n :=
        fun n hn =>
          hgamma_ne ((Complex.Gamma_eq_zero_iff
            (Complex.fixedRealPartVerticalPoint a b)).mpr ⟨n, hn⟩)
      have hpoint_cont :
          ContinuousAt (fun x : ℝ => Complex.fixedRealPartVerticalPoint a x) b := by
        exact Complex.continuousAt_fixedRealPartVerticalPoint_height a b
      have hgamma_cont :
          ContinuousAt
            (fun x : ℝ => Complex.Gamma (Complex.fixedRealPartVerticalPoint a x))
            b :=
        (Complex.differentiableAt_Gamma
          (Complex.fixedRealPartVerticalPoint a b) hpole_free).continuousAt.comp
          hpoint_cont
      have hnum_cont :
          ContinuousAt
            (fun x : ℝ => ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a x)‖)
            b :=
        hgamma_cont.norm
      have hbase_pos : 0 < 1 + ‖b‖ :=
        lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (norm_nonneg b))
      have henv_cont :
          ContinuousAt
            (fun x : ℝ => Complex.fixedRealPartVerticalStirlingEnvelope a x)
            b := by
        exact Complex.continuousAt_fixedRealPartVerticalStirlingEnvelope_height a b
      have henv_ne :
          Complex.fixedRealPartVerticalStirlingEnvelope a b ≠ 0 :=
        ne_of_gt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)
      (hnum_cont.div henv_cont henv_ne).continuousWithinAt

/-- The upper ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaUpperRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The lower ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The fixed-line Gamma ratio is nonnegative on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_nonneg_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (_hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hnum_nonneg :
      0 ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_nonneg (Complex.Gamma (Complex.fixedRealPartVerticalPoint a b))
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  have hden_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    le_of_lt hden_pos
  exact div_nonneg hnum_nonneg hden_nonneg

/-- The fixed-line Gamma ratio is positive on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 < Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hgamma_ne :
      Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
    Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
  have hnum_pos :
      0 < ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_pos_iff.mpr hgamma_ne
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  exact div_pos hnum_pos hden_pos

/-- Compact-height upper ratio has a positive global upper bound. -/
theorem Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
    (a H : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.fixedRealPartVerticalCompactHeightSet_isCompact H)
      (Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
        a H) with
  | ⟨M, hM⟩ =>
  let C : ℝ := max 1 M
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  exact
    ⟨C, hC_pos,
      fun b hb =>
        calc
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤
              ‖Complex.fixedRealPartVerticalGammaUpperRatio a b‖ := by
            exact le_trans
              (le_abs_self (Complex.fixedRealPartVerticalGammaUpperRatio a b))
              (le_of_eq
                (Real.norm_eq_abs
                  (Complex.fixedRealPartVerticalGammaUpperRatio a b)).symm)
          _ ≤ M := hM b hb
          _ ≤ C := le_max_right 1 M⟩

/-- Compact-height lower ratio has a positive global lower bound. -/
theorem Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
    (a H : ℝ)
    (hH_half : (1 / 2 : ℝ) ≤ H) :
    ∃ c : ℝ,
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hcompact :
      IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.fixedRealPartVerticalCompactHeightSet_isCompact H
  have hnonempty :
      (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty :=
    Complex.fixedRealPartVerticalCompactHeightSet_nonempty hH_half
  have hcont :
      ContinuousOn
        (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
        (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
      a H
  match hcompact.exists_isMinOn hnonempty hcont with
  | ⟨b₀, hb₀, hb₀_min⟩ =>
  let c : ℝ := Complex.fixedRealPartVerticalGammaLowerRatio a b₀
  have hc_pos : 0 < c :=
    Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight a H hb₀
  exact
    ⟨c, hc_pos, fun b hb => hb₀_min hb⟩

/-- Canonical compact-height ratio theorem for a fixed vertical line.

The proof is the standard compactness argument: the height set is compact,
the Gamma ratio is continuous there, `Gamma` has no zeros on it because
`|b| ≥ 1/2`, and the fixed-line Stirling envelope is strictly positive. -/
theorem Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds
    (a H : ℝ)
    (hH_pos : 0 < H)
    [hH_half_dec : Decidable ((1 / 2 : ℝ) ≤ H)] :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  match Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
      a H with
  | ⟨C, hC_pos, hC⟩ =>
  if hH_half : (1 / 2 : ℝ) ≤ H then
    match Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
        a H hH_half with
    | ⟨c, hc_pos, hc⟩ =>
    exact ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hC b hb, hc b hb⟩⟩
  else
    have hhalf_lt_H : H < (1 / 2 : ℝ) :=
      lt_of_not_ge hH_half
    have hone_pos : (0 : ℝ) < 1 :=
      zero_lt_one
    exact
      ⟨C, 1, hC_pos, hone_pos,
        fun b hb =>
          have hle : (1 / 2 : ℝ) ≤ H :=
            le_trans hb.1 hb.2
          False.elim ((not_lt_of_ge hle) hhalf_lt_H)⟩

/-- Ratio bounds on the compact-height part of a fixed vertical line.

This is the compactness/nonvanishing owner certificate: local regularity supplies a
finite upper bound for the upper ratio, while nonvanishing of `Γ` and the
strictly positive Stirling envelope supply a positive lower bound. -/
theorem Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  exact Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds a H hH_pos

/-- Ratio bounds give two-sided envelope bounds on the compact-height
part of a fixed vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
    (a H C c : ℝ)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c)
    (hratio :
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b) :
    ∀ b : ℝ,
      (1 / 2 : ℝ) ≤ ‖b‖ →
      ‖b‖ ≤ H →
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact
    fun b hb_inner hb_outer =>
      have hb_mem :
          b ∈ Complex.fixedRealPartVerticalCompactHeightSet H :=
        ⟨hb_inner, hb_outer⟩
      have hratio_b :
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
            c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b :=
        hratio b hb_mem
      have hE_pos :
          0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
        Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
      have hE_nonneg :
          0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
        le_of_lt hE_pos
      have hupper_div :
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
              Complex.fixedRealPartVerticalStirlingEnvelope a b ≤ C :=
        hratio_b.1
      have hlower_div :
          c ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
              Complex.fixedRealPartVerticalStirlingEnvelope a b :=
        hratio_b.2
      have hupper :
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
        (div_le_iff₀ hE_pos).mp hupper_div
      have hlower :
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
        (le_div_iff₀ hE_pos).mp hlower_div
      ⟨hupper, hlower⟩

/-- Compact-height patch for fixed-real-part vertical Stirling bounds.

On the compact set `1 / 2 ≤ |b| ≤ H`, local regularity and nonvanishing of `Γ` on
the fixed vertical line give finite upper and positive lower constants relative
to the positive fixed-line Stirling envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        (1 / 2 : ℝ) ≤ ‖b‖ →
        ‖b‖ ≤ H →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
      a H hH_pos with
  | ⟨C, c, hC_pos, hc_pos, hratio⟩ =>
  exact
    ⟨C, c, hC_pos, hc_pos,
      Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
        a H C c hC_pos hc_pos hratio⟩

/-- Assembly of large-height fixed-line Stirling and compact-height patching. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
    (a : ℝ)
    (hlarge :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          H ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖)
    (hcompact :
      ∀ H : ℝ,
        0 < H →
          ∃ C : ℝ, ∃ c : ℝ,
            0 < C ∧
            0 < c ∧
            ∀ b : ℝ,
              (1 / 2 : ℝ) ≤ ‖b‖ →
              ‖b‖ ≤ H →
                ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
                  C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
                c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖)
    (_hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match hlarge with
  | ⟨H, Clarge, clarge, hH_pos, hClarge_pos, hclarge_pos, hlarge_bound⟩ =>
  match hcompact H hH_pos with
  | ⟨Ccompact, ccompact, hCcompact_pos, hccompact_pos, hcompact_bound⟩ =>
  let C : ℝ := max Clarge Ccompact
  let c : ℝ := min clarge ccompact
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Ccompact)
  have hc_pos : 0 < c :=
    lt_min hclarge_pos hccompact_pos
  exact
    ⟨C, c, hC_pos, hc_pos,
      fun b hb =>
        have hE_nonneg :
            0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
          Complex.fixedRealPartVerticalStirlingEnvelope_nonneg a b
        match height_split_dec H b with
        | isTrue hb_large =>
          have hlarge_b :
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
                  Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
                clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
            hlarge_bound b hb_large
          have hupper_constant :
              Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            mul_le_mul_of_nonneg_right (le_max_left Clarge Ccompact) hE_nonneg
          have hlower_constant :
              c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            mul_le_mul_of_nonneg_right (min_le_left clarge ccompact) hE_nonneg
          ⟨le_trans hlarge_b.1 hupper_constant,
            le_trans hlower_constant hlarge_b.2⟩
        | isFalse hb_large =>
          have hb_compact_upper : ‖b‖ ≤ H :=
            le_of_not_ge hb_large
          have hcompact_b :
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
                  Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
                ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
            hcompact_bound b hb hb_compact_upper
          have hupper_constant :
              Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            mul_le_mul_of_nonneg_right (le_max_right Clarge Ccompact) hE_nonneg
          have hlower_constant :
              c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            mul_le_mul_of_nonneg_right (min_le_right clarge ccompact) hE_nonneg
          ⟨le_trans hcompact_b.1 hupper_constant,
            le_trans hlower_constant hcompact_b.2⟩⟩

/-- Fixed-real-part vertical two-sided Stirling bounds for `Complex.Gamma`.

This is the exact fixed-line specialization theorem in the classical Stirling
API.  Deriving it from the sectorial exponential asymptotic requires the full
vertical-line argument analysis of
`w ^ ((1 / 2 : ℂ) - w)`, including the `exp (-π |b| / 2)` factor and matching
lower bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact
    Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
      a
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
        hbranch a)
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
        a)
      hcompact_half_dec
      height_split_dec

/-- Two-sided fixed-real-part vertical Stirling envelope for `Complex.Gamma`.

This is the fixed-line specialization of sectorial complex Stirling after
separating the argument of `a + i b`: it supplies the matching
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` upper and lower envelopes on every
fixed real line.  The public one-sided estimates below are just projections
from this two-sided classical input. -/
theorem Complex.fixedLineVerticalGammaTwoSidedEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ, ∃ c : ℝ,
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec a =>
    Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
      hbranch a hcompact_half_dec height_split_dec

/-- Standard sectorial `log Γ` Stirling upper bound on the closed right half-plane.

This is the logarithmic special-function root after peeling the downstream
growth theory: Stirling's expansion for `log Γ(w)` on a closed sector avoiding
the negative real axis gives a uniform
`O((1 + ‖w‖) log (2 + ‖w‖))` bound on the closed right half-plane; cf. DLMF
§5.11. The bound is stated for `log ‖Γ(w)‖`, the real part of `log Γ(w)`, so
later Gamma-real normalization steps do not need a branch of `logGamma`. -/
theorem Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  match Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane hbranch with
  | ⟨C, hC_pos, hbound⟩ =>
    have hcoh :
        Complex.BinetSecondFormulaBranchCoherence :=
      Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
    exact
      ⟨C, hC_pos,
        fun w hw_re_pos hw_sector hw_norm =>
          hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩

/-- Fixed-line vertical upper envelope for `Complex.Gamma`.

For each fixed real part `a`, Stirling's formula on the vertical line
`a + i b` gives exponential decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaUpperEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  exact
    fun a =>
      match Complex.fixedLineVerticalGammaTwoSidedEnvelope
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
        ⟨C, hC_pos, fun b hb => (hbounds b hb).1⟩

/-- Fixed-real-part vertical Stirling upper bound for `Complex.Gamma`.

This is the direct fixed-line classical estimate: for each fixed real part `a`,
`Γ(a + i b)` has vertical decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  intro a
  match Complex.fixedLineVerticalGammaUpperEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨C, hC_pos, hupper⟩ =>
    exact
      ⟨C, hC_pos, fun b hb =>
        calc
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ =
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := rfl
          _ ≤ C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            hupper b hb
          _ = C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := by
            exact
              (mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
                ((1 + ‖b‖) ^ (a - 1 / 2))).symm⟩

/-- Fixed-line vertical lower envelope for `Complex.Gamma`.

For each fixed real part `a`, the lower half of vertical Stirling gives the
matching positive constant in front of the same exponential-polynomial
envelope; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaLowerEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  exact
    fun a =>
      match Complex.fixedLineVerticalGammaTwoSidedEnvelope
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
        ⟨c, hc_pos, fun b hb => (hbounds b hb).2⟩

/-- Fixed-real-part vertical Stirling lower bound for `Complex.Gamma`.

This is the lower half of the classical fixed-line estimate, isolated so the
reciprocal estimate is a norm-order transport rather than an independent
primitive. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  intro a
  match Complex.fixedLineVerticalGammaLowerEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨c, hc_pos, hlower⟩ =>
    exact
      ⟨c, hc_pos, fun b hb =>
        calc
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) =
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
            exact
              mul_assoc c (Real.exp (-(Real.pi / 2) * ‖b‖))
                ((1 + ‖b‖) ^ (a - 1 / 2))
          _ ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
            hlower b hb
          _ = ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := rfl⟩

/-- Two-sided fixed-real-part vertical Stirling bounds for `Complex.Gamma`, with the
fixed-line point and envelope named by the owner API.

This is the reusable bundled form of the classical fixed-line asymptotic estimates:
downstream reciprocal and quotient arguments should consume this statement rather
than repeatedly unpacking the two split roots. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match Complex.fixedLineVerticalGammaUpperEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨C, hC_pos, hupper⟩ =>
  match Complex.fixedLineVerticalGammaLowerEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨c, hc_pos, hlower⟩ =>
  exact
    ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hupper b hb, hlower b hb⟩⟩

/-- Classical Gamma/Stirling owner package on the closed right half-plane.

This package is now only product assembly from the canonical local
special-function roots above: sectorial exponential Stirling, its log-norm
consequence, and the two fixed-real-part vertical estimates. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_package_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2)) ∧
    (∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  have hcoh :
      Complex.BinetSecondFormulaBranchCoherence :=
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
  have hexp :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          0 < w.re →
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖ := by
    match Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical hbranch with
    | ⟨R, K, hR_pos, hK_pos, hbound⟩ =>
      exact
        ⟨R, K, hR_pos, hK_pos,
          fun w hw_re_pos hw_sector hw_norm =>
            hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩
  exact
    ⟨hexp,
      Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch,
      Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical
        hbranch hcompact_half_dec height_split_dec,
      Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical
        hbranch hcompact_half_dec height_split_dec⟩

/-- Sectorial log-norm consequence of closed-sector logarithmic Stirling for
`Complex.Gamma` on the closed right half-plane. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch =>
  Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch

/-- `Complex.Gamma` is nonzero on fixed vertical lines away from the real-axis
pole convention when `|b| ≥ 1/2`. -/
theorem Complex.Gamma_fixedRealPart_vertical_ne_zero_of_half_le_norm
    (a b : ℝ)
    (hb : (1 / 2 : ℝ) ≤ ‖b‖) :
    Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
  exact
    fun hzero =>
      match (Complex.Gamma_eq_zero_iff ((a : ℂ) + (b : ℂ) * Complex.I)).mp hzero with
      | ⟨n, hn⟩ =>
        have him_eq : (((a : ℂ) + (b : ℂ) * Complex.I).im) = (-(n : ℂ)).im :=
          congrArg Complex.im hn
        have hleft_im :
            (((a : ℂ) + (b : ℂ) * Complex.I).im) = b := by
          have hmul_im : ((b : ℂ) * Complex.I).im = b :=
            Complex.mul_I_im (b : ℂ)
          have hadd_im :
              (((a : ℂ) + (b : ℂ) * Complex.I).im) =
                (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
            Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
          have hofReal_im : (a : ℂ).im = 0 :=
            Complex.ofReal_im a
          have hsum_eq : (a : ℂ).im + ((b : ℂ) * Complex.I).im = 0 + b :=
            congrArg₂ HAdd.hAdd hofReal_im hmul_im
          calc
            (((a : ℂ) + (b : ℂ) * Complex.I).im) =
                (a : ℂ).im + ((b : ℂ) * Complex.I).im := hadd_im
            _ = 0 + b := hsum_eq
            _ = b := zero_add b
        have hright_im : (-(n : ℂ)).im = 0 := by
          calc
            (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
            _ = 0 := neg_zero
        have hb_zero : b = 0 :=
          Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
        have hnorm_zero : ‖b‖ = 0 :=
          Eq.trans (congrArg norm hb_zero) (norm_zero : ‖(0 : ℝ)‖ = 0)
        have hhalf_pos : (0 : ℝ) < 1 / 2 :=
          half_pos zero_lt_one
        have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
          not_le.mpr hhalf_pos
        have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 := by
          calc
            (1 / 2 : ℝ) ≤ ‖b‖ := hb
            _ = 0 := hnorm_zero
        hnot hhalf_le_zero

/-- Reciprocal transport for fixed-real-part vertical Gamma estimates.

A lower Stirling bound and nonvanishing of `Γ(a + i b)` imply the corresponding
upper bound for the reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound
    {a c : ℝ}
    (hc_pos : 0 < c)
    (hlower :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        c * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ≤
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
        c⁻¹ * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact
    fun b hb =>
      let x : ℝ := (Real.pi / 2) * ‖b‖
      let H : ℝ := 1 + ‖b‖
      let G : ℂ := Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)
      have hH_pos : 0 < H :=
        lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (norm_nonneg b))
      have hexp_pos : 0 < Real.exp (-x) :=
        Real.exp_pos (-x)
      have hrpow_pos : 0 < H ^ (a - 1 / 2) :=
        Real.rpow_pos_of_pos hH_pos (a - 1 / 2)
      have henvelope_pos :
          0 < c * Real.exp (-x) * H ^ (a - 1 / 2) :=
        mul_pos (mul_pos hc_pos hexp_pos) hrpow_pos
      have hG_lower :
          c * Real.exp (-x) * H ^ (a - 1 / 2) ≤ ‖G‖ := by
        have hx_def : x = (Real.pi / 2) * ‖b‖ := rfl
        have hH_def : H = 1 + ‖b‖ := rfl
        calc
          c * Real.exp (-x) * H ^ (a - 1 / 2) =
              c * Real.exp (-((Real.pi / 2) * ‖b‖)) *
                H ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp (-u) * H ^ (a - 1 / 2))
                hx_def
          _ = c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                H ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp u * H ^ (a - 1 / 2))
                (neg_mul (Real.pi / 2) ‖b‖).symm
          _ = c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ =>
                  c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    u ^ (a - 1 / 2))
                hH_def
          _ ≤ ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ :=
            hlower b hb
          _ = ‖G‖ := rfl
      have hG_inv_norm :
          ‖G⁻¹‖ = ‖G‖⁻¹ :=
        norm_inv G
      have hreciprocal_le :
          ‖G‖⁻¹ ≤ (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ :=
        inv_le_inv_of_le henvelope_pos hG_lower
      have htarget_eq :
          (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
            c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := by
        have hexp_neg_eq : Real.exp (-x) = (Real.exp x)⁻¹ :=
          Real.exp_neg x
        have hexp_neg_inv_eq : (Real.exp (-x))⁻¹ = Real.exp x := by
          calc
            (Real.exp (-x))⁻¹ = ((Real.exp x)⁻¹)⁻¹ :=
              congrArg Inv.inv hexp_neg_eq
            _ = Real.exp x := inv_inv (Real.exp x)
        have hpow_neg_eq :
            H ^ (1 / 2 - a) = (H ^ (a - 1 / 2))⁻¹ := by
          have hneg : 1 / 2 - a = -(a - 1 / 2) := by
            exact (neg_sub a (1 / 2)).symm
          exact Eq.trans
            (congrArg (fun y : ℝ => H ^ y) hneg)
            (Real.rpow_neg (le_of_lt hH_pos) (a - 1 / 2))
        calc
          (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
              (H ^ (a - 1 / 2))⁻¹ * (c * Real.exp (-x))⁻¹ := by
                exact mul_inv_rev (c * Real.exp (-x)) (H ^ (a - 1 / 2))
          _ = (H ^ (a - 1 / 2))⁻¹ *
              ((Real.exp (-x))⁻¹ * c⁻¹) := by
                exact congrArg
                  (fun y : ℝ => (H ^ (a - 1 / 2))⁻¹ * y)
                  (mul_inv_rev c (Real.exp (-x)))
          _ = c⁻¹ * (Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹ := by
                calc
                  (H ^ (a - 1 / 2))⁻¹ *
                      ((Real.exp (-x))⁻¹ * c⁻¹) =
                    ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) * c⁻¹ :=
                      (mul_assoc (H ^ (a - 1 / 2))⁻¹ (Real.exp (-x))⁻¹ c⁻¹).symm
                  _ = c⁻¹ *
                      ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) :=
                    mul_comm ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) c⁻¹
                  _ = c⁻¹ *
                      ((Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹) := by
                    exact congrArg
                      (fun y : ℝ => c⁻¹ * y)
                      (mul_comm (H ^ (a - 1 / 2))⁻¹ (Real.exp (-x))⁻¹)
                  _ = c⁻¹ * (Real.exp (-x))⁻¹ *
                      (H ^ (a - 1 / 2))⁻¹ :=
                    (mul_assoc c⁻¹ (Real.exp (-x))⁻¹
                      (H ^ (a - 1 / 2))⁻¹).symm
          _ = (c⁻¹ * Real.exp x) * (H ^ (a - 1 / 2))⁻¹ := by
                exact congrArg
                  (fun y : ℝ => (c⁻¹ * y) * (H ^ (a - 1 / 2))⁻¹)
                  hexp_neg_inv_eq
          _ = (c⁻¹ * Real.exp x) * H ^ (1 / 2 - a) := by
                exact congrArg
                  (fun y : ℝ => (c⁻¹ * Real.exp x) * y)
                  hpow_neg_eq.symm
          _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := rfl
      calc
        ‖G⁻¹‖ = ‖G‖⁻¹ := hG_inv_norm
        _ ≤ (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ :=
          hreciprocal_le
        _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) :=
          htarget_eq

/-- Reciprocal transport for vertical-strip Gamma estimates.

A uniform lower Stirling bound on a real strip gives the matching reciprocal
upper bound on the same large-height region. -/

/-- Fixed-real-part reciprocal vertical Stirling bound for `Complex.Gamma`, obtained
from the lower fixed-line estimate by reciprocal transport. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
    fun a =>
      match Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨c, hc_pos, hlower⟩ =>
        ⟨c⁻¹, inv_pos.mpr hc_pos,
          Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound hc_pos hlower⟩

/-- Fixed-real-part vertical Stirling bounds for `Complex.Gamma` and its
reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
    fun a =>
      match Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨Cu, hCu_pos, hCu⟩ =>
      match Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨Cr, hCr_pos, hCr⟩ =>
      let C : ℝ := Cu + Cr
      have hC_pos : 0 < C :=
        add_pos hCu_pos hCr_pos
      have hCu_le_C : Cu ≤ C :=
        le_add_of_nonneg_right (le_of_lt hCr_pos)
      have hCr_le_C : Cr ≤ C :=
        le_add_of_nonneg_left (le_of_lt hCu_pos)
      ⟨C, hC_pos,
        fun b hb =>
          have hdirect_envelope_nonneg :
              0 ≤ Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) := by
            have hbase_pos : 0 < 1 + ‖b‖ :=
              lt_of_lt_of_le zero_lt_one
                (le_add_of_nonneg_right (norm_nonneg b))
            exact mul_nonneg
              (le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖b‖)))
              (le_of_lt (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2)))
          have hreciprocal_envelope_nonneg :
              0 ≤ Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a) := by
            have hbase_pos : 0 < 1 + ‖b‖ :=
              lt_of_lt_of_le zero_lt_one
                (le_add_of_nonneg_right (norm_nonneg b))
            exact mul_nonneg
              (le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖b‖)))
              (le_of_lt (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a)))
          have hdirect_scaled :
              Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2)) ≤
                C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2)) :=
            mul_le_mul_of_nonneg_right hCu_le_C hdirect_envelope_nonneg
          have hreciprocal_scaled :
              Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a)) ≤
                C * (Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a)) :=
            mul_le_mul_of_nonneg_right hCr_le_C hreciprocal_envelope_nonneg
          have hdirect_source_assoc :
              Cu * Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2) =
                Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2)) :=
            mul_assoc Cu (Real.exp (-(Real.pi / 2) * ‖b‖))
              ((1 + ‖b‖) ^ (a - 1 / 2))
          have hdirect_target_assoc :
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2) =
                C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (a - 1 / 2)) :=
            mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
              ((1 + ‖b‖) ^ (a - 1 / 2))
          have hreciprocal_source_assoc :
              Cr * Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a) =
                Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a)) :=
            mul_assoc Cr (Real.exp ((Real.pi / 2) * ‖b‖))
              ((1 + ‖b‖) ^ (1 / 2 - a))
          have hreciprocal_target_assoc :
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a) =
                C * (Real.exp ((Real.pi / 2) * ‖b‖) *
                  (1 + ‖b‖) ^ (1 / 2 - a)) :=
            mul_assoc C (Real.exp ((Real.pi / 2) * ‖b‖))
              ((1 + ‖b‖) ^ (1 / 2 - a))
          And.intro
            (calc
              ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
                  Cu * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2) :=
                hCu b hb
              _ = Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2)) :=
                hdirect_source_assoc
              _ ≤ C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2)) :=
                hdirect_scaled
              _ = C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2) :=
                hdirect_target_assoc.symm)
            (calc
              ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
                  Cr * Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a) :=
                hCr b hb
              _ = Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a)) :=
                hreciprocal_source_assoc
              _ ≤ C * (Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a)) :=
                hreciprocal_scaled
              _ = C * Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a) :=
                hreciprocal_target_assoc.symm)⟩

/-- Classical closed-sector Stirling expansion for `Complex.Gamma`, with the
sectorial and fixed-line consequences used by the normalization chain.

This owner theorem is now only the product assembly of the formula-level
Stirling input, its sectorial log-norm consequence, and the fixed-line vertical
estimates; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a)) := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  have hcoh :
      Complex.BinetSecondFormulaBranchCoherence :=
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
  have hexp :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          0 < w.re →
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖ := by
    match Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical hbranch with
    | ⟨R, K, hR_pos, hK_pos, hbound⟩ =>
      exact
        ⟨R, K, hR_pos, hK_pos,
          fun w hw_re_pos hw_sector hw_norm =>
            hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩
  exact
    ⟨hexp,
      Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch,
      Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical
        hbranch hcompact_half_dec height_split_dec⟩

/- Classical closed-sector Stirling estimates for `Complex.Gamma` are packaged
above by
`Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical`;
cf. DLMF §5.11. -/


end
end LFunctions
end Boundary
