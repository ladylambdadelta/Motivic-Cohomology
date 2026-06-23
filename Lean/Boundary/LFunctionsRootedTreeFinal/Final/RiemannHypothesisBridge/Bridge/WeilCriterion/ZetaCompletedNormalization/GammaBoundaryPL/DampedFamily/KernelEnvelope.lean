import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.BoundaryNormalization

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

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
  let S : ℝ := |a| + |b| + 2
  let R : ℝ := 4 * ((N + 1 : ℕ) : ℝ) * S + 1
  let K : ℝ := R + 2 * S + 1
  have hS_nonneg : 0 ≤ S := by
    have habs_sum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    exact le_trans zero_le_two (le_add_of_nonneg_left habs_sum_nonneg)
  have hN_nonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg (N + 1)
  have hR_pos : 0 < R := by
    have hshift_nonneg : 0 ≤ 4 * ((N + 1 : ℕ) : ℝ) * S :=
      mul_nonneg
        (mul_nonneg (le_of_lt zero_lt_four) hN_nonneg)
        hS_nonneg
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hshift_nonneg)
  have htwoS_nonneg : 0 ≤ 2 * S :=
    mul_nonneg zero_le_two hS_nonneg
  have hK_pos : 0 < K := by
    have hR_le_R_twoS : R ≤ R + 2 * S :=
      le_add_of_nonneg_right htwoS_nonneg
    have hR_twoS_le_K : R + 2 * S ≤ K :=
      le_add_of_nonneg_right zero_le_one
    exact lt_of_lt_of_le hR_pos (le_trans hR_le_R_twoS hR_twoS_le_K)
  exact
    ⟨K, hK_pos,
      fun z hza hzb hzim =>
        have hbase_norm_abs :
            ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ =
              Complex.abs
                (verticalStripUpperTailDegreePolynomialBase a b N z) :=
          Complex.norm_eq_abs
            (verticalStripUpperTailDegreePolynomialBase a b N z)
        have hnorm_coord :
            Complex.abs
                (verticalStripUpperTailDegreePolynomialBase a b N z) ≤
              |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
                |(verticalStripUpperTailDegreePolynomialBase a b N z).im| :=
          Complex.abs_le_abs_re_add_abs_im
            (verticalStripUpperTailDegreePolynomialBase a b N z)
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
        have hcoord_bound :
            |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
                |(verticalStripUpperTailDegreePolynomialBase a b N z).im| ≤
              R + ‖z‖ + 2 * S := by
          calc
            |(verticalStripUpperTailDegreePolynomialBase a b N z).re| +
                |(verticalStripUpperTailDegreePolynomialBase a b N z).im|
                = (verticalStripUpperTailDegreePolynomialBase a b N z).re +
                    |(verticalStripUpperTailDegreePolynomialBase a b N z).im| := by
              exact congrArg
                (fun x : ℝ =>
                  x +
                    |(verticalStripUpperTailDegreePolynomialBase a b N z).im|)
                hre_abs
            _ = (R + z.im) +
                    |(verticalStripUpperTailDegreePolynomialBase a b N z).im| := by
              exact congrArg
                (fun x : ℝ =>
                  x +
                    |(verticalStripUpperTailDegreePolynomialBase a b N z).im|)
                hre_eq
            _ ≤ (R + ‖z‖) + 2 * S :=
              add_le_add
                (add_le_add_left hzim_le_norm R)
                him_bound
            _ = R + ‖z‖ + 2 * S :=
              add_assoc R ‖z‖ (2 * S)
        have hK_expand :
            K * (1 + ‖z‖) = K + K * ‖z‖ := by
          calc
            K * (1 + ‖z‖) = K * 1 + K * ‖z‖ := mul_add K 1 ‖z‖
            _ = K + K * ‖z‖ := by
              exact congrArg (fun x : ℝ => x + K * ‖z‖) (mul_one K)
        have hconstant_le_K : R + ‖z‖ + 2 * S ≤ K + K * ‖z‖ := by
          have hnorm_nonneg : 0 ≤ ‖z‖ :=
            norm_nonneg z
          have hone_le_K : 1 ≤ K := by
            have hR_one_le_K : R + 1 ≤ K := by
              calc
                R + 1 ≤ R + 2 * S + 1 :=
                  add_le_add_right (le_add_of_nonneg_right htwoS_nonneg) 1
                _ = K := by
                  exact (add_assoc R (2 * S) 1).symm
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
        Eq.subst
          (motive := fun T : ℝ =>
            ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ≤ T)
          hK_expand.symm
          (le_trans
            (Eq.subst
              (motive := fun T : ℝ => T ≤ R + ‖z‖ + 2 * S)
              hbase_norm_abs
              (le_trans hnorm_coord hcoord_bound))
            hconstant_le_K)⟩

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
      have hK_nonneg : 0 ≤ K :=
        le_of_lt hK_pos
      exact
        ⟨K ^ N, pow_pos hK_pos N,
          fun z hza hzb hzim =>
            have hkernel_le_base :
                (verticalStripUpperTailDegreePolynomialKernel a b N z).re ≤
                  ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N :=
              verticalStripUpperTailDegreePolynomialKernel_re_le_base_norm_pow
                a b N z
            have hbase_bound :
                ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N ≤
                  (K * (1 + ‖z‖)) ^ N :=
              pow_le_pow_left₀
                (norm_nonneg
                  (verticalStripUpperTailDegreePolynomialBase a b N z))
                (hbase z hza hzb hzim)
                N
            have hmul_pow :
                (K * (1 + ‖z‖)) ^ N =
                  K ^ N * (1 + ‖z‖) ^ N :=
              mul_pow K (1 + ‖z‖) N
            le_trans hkernel_le_base
              (Eq.subst
                (motive := fun T : ℝ =>
                  ‖verticalStripUpperTailDegreePolynomialBase a b N z‖ ^ N ≤ T)
                hmul_pow
                hbase_bound)⟩

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
      exact
        ⟨B, hB_pos,
          fun z hza hzb hzim =>
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
            have hcoef_le : C * K ≤ B :=
              le_add_of_nonneg_right zero_le_one
            have hcoef_scaled :
                (C * K) * (1 + ‖z‖) ^ N ≤
                  B * (1 + ‖z‖) ^ N :=
              mul_le_mul_of_nonneg_right hcoef_le hpow_nonneg
            le_trans hscaled
              (Eq.subst
                (motive := fun T : ℝ => T ≤ B * (1 + ‖z‖) ^ N)
                hscaled_assoc
                hcoef_scaled)⟩

end
end LFunctions
end Boundary
