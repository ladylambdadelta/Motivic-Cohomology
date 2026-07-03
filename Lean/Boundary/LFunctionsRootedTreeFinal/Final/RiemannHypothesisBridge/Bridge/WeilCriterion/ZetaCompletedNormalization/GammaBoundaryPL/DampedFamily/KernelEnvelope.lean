import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.BoundaryNormalization

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- Width constant for the degree-polynomial base on the strip `[a,b]`. -/
def verticalStripUpperTailDegreePolynomialBaseWidth (a b : ℝ) : ℝ :=
  |a| + |b| + 2

/-- Real-part offset for the degree-polynomial base on the strip `[a,b]`. -/
def verticalStripUpperTailDegreePolynomialBaseOffset
    (a b : ℝ)
    (N : ℕ) : ℝ :=
  4 * ((N + 1 : ℕ) : ℝ) *
      verticalStripUpperTailDegreePolynomialBaseWidth a b + 1

/-- Affine norm envelope constant for the degree-polynomial base. -/
def verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant
    (a b : ℝ)
    (N : ℕ) : ℝ :=
  verticalStripUpperTailDegreePolynomialBaseOffset a b N +
    2 * verticalStripUpperTailDegreePolynomialBaseWidth a b + 1

/-- The strip width constant is nonnegative. -/
theorem verticalStripUpperTailDegreePolynomialBaseWidth_nonneg
    (a b : ℝ) :
    0 ≤ verticalStripUpperTailDegreePolynomialBaseWidth a b := by
  have habs_sum_nonneg : 0 ≤ |a| + |b| :=
    add_nonneg (abs_nonneg a) (abs_nonneg b)
  exact le_trans zero_le_two (le_add_of_nonneg_left habs_sum_nonneg)

/-- The degree-polynomial base offset is positive. -/
theorem verticalStripUpperTailDegreePolynomialBaseOffset_pos
    (a b : ℝ)
    (N : ℕ) :
    0 < verticalStripUpperTailDegreePolynomialBaseOffset a b N := by
  have hwidth_nonneg :
      0 ≤ verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    verticalStripUpperTailDegreePolynomialBaseWidth_nonneg a b
  have hN_nonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  have hshift_nonneg :
      0 ≤ 4 * ((N + 1 : ℕ) : ℝ) *
        verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    mul_nonneg
      (mul_nonneg (le_of_lt zero_lt_four) hN_nonneg)
      hwidth_nonneg
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hshift_nonneg)

/-- The degree-polynomial base affine envelope constant is positive. -/
theorem verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant_pos
    (a b : ℝ)
    (N : ℕ) :
    0 < verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N := by
  have hwidth_nonneg :
      0 ≤ verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    verticalStripUpperTailDegreePolynomialBaseWidth_nonneg a b
  have hR_pos :
      0 < verticalStripUpperTailDegreePolynomialBaseOffset a b N :=
    verticalStripUpperTailDegreePolynomialBaseOffset_pos a b N
  have htwo_width_nonneg :
      0 ≤ 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    mul_nonneg zero_le_two hwidth_nonneg
  have hR_le_R_two_width :
      verticalStripUpperTailDegreePolynomialBaseOffset a b N ≤
        verticalStripUpperTailDegreePolynomialBaseOffset a b N +
          2 * verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    le_add_of_nonneg_right htwo_width_nonneg
  have hR_two_width_le_K :
      verticalStripUpperTailDegreePolynomialBaseOffset a b N +
          2 * verticalStripUpperTailDegreePolynomialBaseWidth a b ≤
        verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N :=
    le_add_of_nonneg_right zero_le_one
  exact lt_of_lt_of_le hR_pos
    (le_trans hR_le_R_two_width hR_two_width_le_K)

/-- Coordinate estimate for the degree-polynomial base on the upper strip. -/
theorem verticalStripUpperTailDegreePolynomialBase_abs_re_add_abs_im_le
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hzim : 1 ≤ z.im) :
    |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
        |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
      verticalStripUpperTailDegreePolynomialBaseOffset a b N +
        ‖z‖ + 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b := by
  let S : ℝ := verticalStripUpperTailDegreePolynomialBaseWidth a b
  let R : ℝ := verticalStripUpperTailDegreePolynomialBaseOffset a b N
  have hre_pos :
      0 < (verticalStripUpperTailDegreePolynomialBase a b N z).re :=
    verticalStripUpperTailDegreePolynomialBase_re_pos_on_upperTail
      a b N hzim
  have hre_abs :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).re| =
        (verticalStripUpperTailDegreePolynomialBase a b N z).re :=
    abs_of_pos hre_pos
  have hre_eq :
      (verticalStripUpperTailDegreePolynomialBase a b N z).re =
        R + z.im :=
    verticalStripUpperTailDegreePolynomialBase_re a b N z
  have him_bound :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        2 * S :=
    verticalStripUpperTailDegreePolynomialBase_im_abs_le
      a b N hza hzb
  have hzim_le_norm : z.im ≤ ‖z‖ := by
    have hzim_le_abs : z.im ≤ Complex.abs z :=
      Complex.im_le_abs z
    exact
      Eq.subst
        (motive := fun T : ℝ => z.im ≤ T)
        (Complex.norm_eq_abs z).symm
        hzim_le_abs
  calc
    |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
        |(verticalStripUpperTailDegreePolynomialBase a b N z).im|
        = (verticalStripUpperTailDegreePolynomialBase a b N z).re +
            |(verticalStripUpperTailDegreePolynomialBase a b N z).im| := by
      exact congrArg
        (fun x : ℝ =>
          x + |(verticalStripUpperTailDegreePolynomialBase a b N z).im|)
        hre_abs
    _ = (R + z.im) +
            |(verticalStripUpperTailDegreePolynomialBase a b N z).im| := by
      exact congrArg
        (fun x : ℝ =>
          x + |(verticalStripUpperTailDegreePolynomialBase a b N z).im|)
        hre_eq
    _ ≤ (R + ‖z‖) + 2 * S :=
      add_le_add
        (add_le_add_left hzim_le_norm R)
        him_bound

/-- Expands the affine envelope product against `1 + ‖z‖`. -/
theorem verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant_mul_one_add_norm
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
        (1 + ‖z‖) =
      verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N +
        verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
          ‖z‖ := by
  let K : ℝ := verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N
  calc
    K * (1 + ‖z‖) = K * 1 + K * ‖z‖ := mul_add K 1 ‖z‖
    _ = K + K * ‖z‖ := by
      exact congrArg (fun x : ℝ => x + K * ‖z‖) (mul_one K)

/-- The affine coordinate bound is absorbed by the chosen envelope constant. -/
theorem verticalStripUpperTailDegreePolynomialBase_affine_le_envelope_expanded
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ) :
    verticalStripUpperTailDegreePolynomialBaseOffset a b N +
        ‖z‖ + 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b ≤
      verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N +
        verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
          ‖z‖ := by
  let S : ℝ := verticalStripUpperTailDegreePolynomialBaseWidth a b
  let R : ℝ := verticalStripUpperTailDegreePolynomialBaseOffset a b N
  let K : ℝ := verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N
  have hS_nonneg : 0 ≤ S :=
    verticalStripUpperTailDegreePolynomialBaseWidth_nonneg a b
  have hR_pos : 0 < R :=
    verticalStripUpperTailDegreePolynomialBaseOffset_pos a b N
  have htwoS_nonneg : 0 ≤ 2 * S :=
    mul_nonneg zero_le_two hS_nonneg
  have hnorm_nonneg : 0 ≤ ‖z‖ :=
    norm_nonneg z
  have hone_le_K : 1 ≤ K := by
    have hR_one_le_K : R + 1 ≤ K := by
      calc
        R + 1 ≤ R + 2 * S + 1 :=
          add_le_add_right (le_add_of_nonneg_right htwoS_nonneg) 1
        _ = K := by
          rfl
    exact le_trans (le_add_of_nonneg_left (le_of_lt hR_pos)) hR_one_le_K
  have hnorm_le_scaled : ‖z‖ ≤ K * ‖z‖ :=
    le_trans
      (Eq.subst
        (motive := fun T : ℝ => ‖z‖ ≤ T)
        (one_mul ‖z‖).symm
        (le_refl ‖z‖))
      (mul_le_mul_of_nonneg_right hone_le_K hnorm_nonneg)
  calc
    R + ‖z‖ + 2 * S = R + 2 * S + ‖z‖ := by
      calc
        R + ‖z‖ + 2 * S = R + (‖z‖ + 2 * S) :=
          add_assoc R ‖z‖ (2 * S)
        _ = R + (2 * S + ‖z‖) := by
          exact congrArg (fun x : ℝ => R + x)
            (add_comm ‖z‖ (2 * S))
        _ = R + 2 * S + ‖z‖ :=
          (add_assoc R (2 * S) ‖z‖).symm
    _ ≤ R + 2 * S + K * ‖z‖ :=
      add_le_add_left hnorm_le_scaled (R + 2 * S)
    _ ≤ K + K * ‖z‖ :=
      add_le_add_right
        (le_add_of_nonneg_right zero_le_one)
        (K * ‖z‖)

/-- Pointwise affine norm envelope for the degree-polynomial base. -/
theorem verticalStripUpperTailDegreePolynomialBase_norm_le_one_add_norm_envelope_pointwise
    (a b : ℝ)
    (N : ℕ)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hzim : 1 ≤ z.im) :
    ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ≤
      verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
        (1 + ‖z‖) := by
  have hbase_norm_abs :
      ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ =
        Complex.abs (verticalStripUpperTailDegreePolynomialBase a b N z) :=
    Complex.norm_eq_abs (verticalStripUpperTailDegreePolynomialBase a b N z)
  have hnorm_coord :
      Complex.abs (verticalStripUpperTailDegreePolynomialBase a b N z) ≤
        |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
          |(verticalStripUpperTailDegreePolynomialBase a b N z).im| :=
    Complex.abs_le_abs_re_add_abs_im
      (verticalStripUpperTailDegreePolynomialBase a b N z)
  have hcoord_bound :
      |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
          |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
        verticalStripUpperTailDegreePolynomialBaseOffset a b N +
          ‖z‖ + 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b :=
    verticalStripUpperTailDegreePolynomialBase_abs_re_add_abs_im_le
      a b N z hza hzb hzim
  have hK_expand :
      verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
          (1 + ‖z‖) =
        verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N +
          verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
            ‖z‖ :=
    verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant_mul_one_add_norm
      a b N z
  have hconstant_le_K :
      verticalStripUpperTailDegreePolynomialBaseOffset a b N +
          ‖z‖ + 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b ≤
        verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N +
          verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N *
            ‖z‖ :=
    verticalStripUpperTailDegreePolynomialBase_affine_le_envelope_expanded
      a b N z
  exact Eq.subst
    (motive := fun T : ℝ =>
      ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ≤ T)
    hK_expand.symm
    (le_trans
      (Eq.subst
        (motive := fun T : ℝ =>
          T ≤ verticalStripUpperTailDegreePolynomialBaseOffset a b N +
            ‖z‖ + 2 * verticalStripUpperTailDegreePolynomialBaseWidth a b)
        hbase_norm_abs
        (le_trans hnorm_coord hcoord_bound))
      hconstant_le_K)

/-- The tilted degree-polynomial base is bounded by a fixed affine multiple of
`1 + ‖z‖` on every vertical strip. -/
theorem verticalStripUpperTailDegreePolynomialBase_norm_le_one_add_norm_envelope
    (a b : ℝ)
    (N : ℕ) :
    ∃ K : ℝ,
      0 < K ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ≤
          K * (1 + ‖z‖) := by
  exact
    ⟨verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant a b N,
      verticalStripUpperTailDegreePolynomialBaseEnvelopeConstant_pos a b N,
      fun z hza hzb hzim =>
        verticalStripUpperTailDegreePolynomialBase_norm_le_one_add_norm_envelope_pointwise
          a b N z hza hzb hzim⟩

/-- Pointwise power envelope for the real part of the degree-polynomial
kernel, assuming the base affine envelope. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_power_envelope_pointwise
    (a b : ℝ)
    (N : ℕ)
    (K : ℝ)
    (hbase :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ≤
          K * (1 + ‖z‖))
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hzim : 1 ≤ z.im) :
    (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
      K ^ N * (1 + ‖z‖) ^ N := by
  have hkernel_le_base :
      (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
        ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N :=
    verticalStripUpperTailDegreePolynomialKernel_re_le_base_norm_pow
      a b N z
  have hbase_bound :
      ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N ≤
        (K * (1 + ‖z‖)) ^ N :=
    pow_le_pow_left₀
      (norm_nonneg (verticalStripUpperTailDegreePolynomialBase a b N z))
      (hbase z hza hzb hzim)
      N
  have hmul_pow :
      (K * (1 + ‖z‖)) ^ N =
        K ^ N * (1 + ‖z‖) ^ N :=
    mul_pow K (1 + ‖z‖) N
  exact le_trans hkernel_le_base
    (Eq.subst
      (motive := fun T : ℝ =>
        ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N ≤ T)
      hmul_pow
      hbase_bound)

/-- The real part of the degree-polynomial kernel is bounded above by a fixed
power envelope on each closed vertical strip upper tail. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_power_envelope
    (a b : ℝ)
    (N : ℕ) :
    ∃ K : ℝ,
      0 < K ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
          K * (1 + ‖z‖) ^ N := by
  match
    verticalStripUpperTailDegreePolynomialBase_norm_le_one_add_norm_envelope
      a b N
  with
  | ⟨K, hK_pos, hbase⟩ =>
      exact
        ⟨K ^ N, pow_pos hK_pos N,
          fun z hza hzb hzim =>
            verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_power_envelope_pointwise
              a b N K hbase z hza hzb hzim⟩

/-- Pointwise scaled envelope for the degree-polynomial kernel. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_envelope_pointwise
    (a b C : ℝ)
    (N : ℕ)
    (K B : ℝ)
    (hC_nonneg : 0 ≤ C)
    (hkernel :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
          K * (1 + ‖z‖) ^ N)
    (hcoef_le : C * K ≤ B)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hzim : 1 ≤ z.im) :
    C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
      B * (1 + ‖z‖) ^ N := by
  have hpow_nonneg : 0 ≤ (1 + ‖z‖) ^ N :=
    pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) N
  have hscaled :
      C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
        C * (K * (1 + ‖z‖) ^ N) :=
    mul_le_mul_of_nonneg_left (hkernel z hza hzb hzim) hC_nonneg
  have hscaled_assoc :
      C * (K * (1 + ‖z‖) ^ N) =
        (C * K) * (1 + ‖z‖) ^ N :=
    (mul_assoc C K ((1 + ‖z‖) ^ N)).symm
  have hcoef_scaled :
      (C * K) * (1 + ‖z‖) ^ N ≤
        B * (1 + ‖z‖) ^ N :=
    mul_le_mul_of_nonneg_right hcoef_le hpow_nonneg
  exact le_trans hscaled
    (Eq.subst
      (motive := fun T : ℝ => T ≤ B * (1 + ‖z‖) ^ N)
      hscaled_assoc.symm
      hcoef_scaled)

/-- The degree-polynomial upper-tail kernel has finite polynomial growth on
each closed vertical strip.  This is the geometric envelope needed to undamp
the finite-order normalized factor. -/
theorem verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_envelope
    (a b C : ℝ)
    (N : ℕ)
    (hC_nonneg : 0 ≤ C) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        C * (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
          B * (1 + ‖z‖) ^ N := by
  match
    verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_power_envelope
      a b N
  with
  | ⟨K, hK_pos, hkernel⟩ =>
      let B : ℝ := C * K + 1
      have hK_nonneg : 0 ≤ K :=
        le_of_lt hK_pos
      have hCK_nonneg : 0 ≤ C * K :=
        mul_nonneg hC_nonneg hK_nonneg
      have hB_pos : 0 < B :=
        lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hCK_nonneg)
      have hcoef_le : C * K ≤ B :=
        le_add_of_nonneg_right zero_le_one
      exact
        ⟨B, hB_pos,
          fun z hza hzb hzim =>
            verticalStripUpperTailDegreePolynomialKernel_re_le_one_add_norm_envelope_pointwise
              a b C N K B hC_nonneg hkernel hcoef_le z hza hzb hzim⟩

end
end LFunctions
end Boundary
