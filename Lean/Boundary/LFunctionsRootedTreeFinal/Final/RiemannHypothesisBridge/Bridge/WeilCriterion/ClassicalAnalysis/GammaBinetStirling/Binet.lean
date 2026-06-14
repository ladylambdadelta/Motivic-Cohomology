import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMajorant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Binet formula and kernel estimates

This file owns Binet's second logarithmic formula and the real majorant
estimates for its kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The derivative kernel obtained by differentiating
`arctan ((t : ℂ) / w)` in Binet's second-formula remainder. -/
noncomputable def Complex.binetSecondFormulaDerivativeKernel
    (t : ℝ) (w : ℂ) : ℂ :=
  (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The candidate derivative of the Binet second-formula remainder after
differentiating under the integral sign. -/
noncomputable def Complex.binetSecondFormulaRemainderDerivative
    (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetSecondFormulaDerivativeKernel t w

/-- Norm of the Binet exponential denominator agrees with the positive real
denominator. -/
theorem Complex.binetSecondFormula_exp_denominator_norm_eq
    (t : ℝ) :
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
      ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
  calc
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        ‖((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ)‖ := by
      simp [Complex.ofReal_exp, Complex.ofReal_sub]
    _ = ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
      simp [Complex.normSq, Real.norm_eq_abs]

/-- The exact classical positive-real Binet identity in the normalization used
by this file.  This is the classical analytic input; mathlib currently exposes
Gamma integral and Bohr-Mollerup infrastructure but not this arctangent-kernel
Binet formula as a theorem. -/
theorem Complex.Gamma_binetSecondFormula_positiveReal_from_classical_Binet
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  sorry

/-- Classical Binet's second formula on the positive real axis, with the
principal logarithm and the arctangent-kernel remainder as normalized in this
file. -/
theorem Complex.Gamma_binetSecondFormula_positiveReal_classical_identity
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  exact
    Complex.Gamma_binetSecondFormula_positiveReal_from_classical_Binet hx

/-- Binet's second formula on the positive real axis with the principal-log
normalization used in this package.

This is the basepoint/real-axis normalization input for the complex
open-half-plane identity. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  exact
    Complex.Gamma_binetSecondFormula_positiveReal_classical_identity hx

/-- The principal complex arctangent has derivative `1 / (1 + z^2)` at points
where its defining logarithm is differentiable.  The extra `slitPlane`
hypothesis is essential for the principal branch of `Complex.log`. -/
theorem Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
    {z : ℂ}
    (hzI : z ≠ Complex.I)
    (hznegI : z ≠ -Complex.I)
    (hzslit :
      (1 + z * Complex.I) / (1 - z * Complex.I) ∈ Complex.slitPlane) :
    HasDerivAt
      Complex.arctan
      ((1 : ℂ) / (1 + z ^ 2)) z := by
  have hnum_ne : 1 + z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]
        _ = (-1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = -1 := by
            exact add_eq_zero_iff_eq_neg.mp hzero
          rw [hzI_eq]
        _ = Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hzI hz_eq
  have hden_ne : 1 - z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = -Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]
        _ = (1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = 1 := by
            exact sub_eq_zero.mp hzero
          rw [hzI_eq]
        _ = -Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hznegI hz_eq
  let q : ℂ → ℂ :=
    fun u : ℂ => (1 + u * Complex.I) / (1 - u * Complex.I)
  have hq :
      HasDerivAt q
        ((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) z := by
    have hnum :
        HasDerivAt (fun u : ℂ => 1 + u * Complex.I) Complex.I z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
    have hden :
        HasDerivAt (fun u : ℂ => 1 - u * Complex.I) (-Complex.I) z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
    have hdiv := hnum.div hden hden_ne
    simpa [q] using hdiv
  have hlog :
      HasDerivAt
        (fun u : ℂ => Complex.log (q u))
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hq.clog hzslit
  have hscaled :
      HasDerivAt
        (fun u : ℂ => (-Complex.I / 2) * Complex.log (q u))
        ((-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I)))) z :=
    hlog.const_mul (-Complex.I / 2)
  have halg :
      (-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        (1 : ℂ) / (1 + z ^ 2) := by
    have hprod_ne : 1 + z ^ 2 ≠ 0 := by
      have hfactor :
          (1 - z * Complex.I) * (1 + z * Complex.I) = 1 + z ^ 2 := by
        ring_nf
      intro hzero
      exact (mul_ne_zero hden_ne hnum_ne) (hfactor.trans hzero)
    field_simp [hnum_ne, hden_ne, hprod_ne]
    ring_nf
  simpa [Complex.arctan, q, halg]
    using hscaled

/-- A point in the open right half-plane is nonzero. -/
theorem Complex.ne_zero_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ≠ 0 := by
  intro hw
  have hre_zero : w.re = 0 := by
    simpa [hw]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq hre_zero)

/-- Adding a purely imaginary number to a point in the open right half-plane
cannot give zero. -/
theorem Complex.add_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w + (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w + (t : ℂ) * Complex.I).re = 0 := by
    simpa [hzero]
  have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re := by
    simp [Complex.add_re, Complex.mul_re]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- Subtracting a purely imaginary number from a point in the open right
half-plane cannot give zero. -/
theorem Complex.sub_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w - (t : ℂ) * Complex.I).re = 0 := by
    simpa [hzero]
  have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re := by
    simp [Complex.sub_re, Complex.mul_re]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- The algebraic denominator `w^2 + t^2` in the differentiated Binet kernel
does not vanish in the open right half-plane. -/
theorem Complex.binet_arctan_derivative_denominator_ne_zero
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  have hplus :
      w + (t : ℂ) * Complex.I ≠ 0 :=
    Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hminus :
      w - (t : ℂ) * Complex.I ≠ 0 :=
    Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hfactor :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) =
        w ^ 2 + (t : ℂ) ^ 2 := by
    calc
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I)
          = w ^ 2 - ((t : ℂ) * Complex.I) ^ 2 := by
            ring
      _ = w ^ 2 + (t : ℂ) ^ 2 := by
            simp [Complex.I_mul_I]
  intro hzero
  have hprod_zero :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) = 0 :=
    hfactor.trans hzero
  exact
    (mul_ne_zero hplus hminus) hprod_zero

/-- A nonnegative real part gives a lower bound for the complex norm. -/
theorem Complex.re_le_norm_of_nonneg_re
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re) :
    z.re ≤ ‖z‖ := by
  have hre_abs_eq : |z.re| = z.re :=
    abs_of_nonneg hz_re_nonneg
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    simpa [Complex.normSq, norm_eq_abs] using
      Complex.abs_re_le_abs z
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      hre_abs_eq
      hre_abs_le_norm

/-- Adding a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_add_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z + (t : ℂ) * Complex.I‖ := by
  have hsum_re_nonneg : 0 ≤ (z + (t : ℂ) * Complex.I).re := by
    simpa [Complex.add_re, Complex.mul_re] using hz_re_nonneg
  have hnorm :
      (z + (t : ℂ) * Complex.I).re ≤
        ‖z + (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hsum_re_nonneg
  have hre :
      (z + (t : ℂ) * Complex.I).re = z.re := by
    simp [Complex.add_re, Complex.mul_re]
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z + (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Subtracting a purely imaginary real multiple preserves the real-part lower
bound for the complex norm. -/
theorem Complex.re_le_norm_sub_real_mul_I
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (t : ℝ) :
    z.re ≤ ‖z - (t : ℂ) * Complex.I‖ := by
  have hdiff_re_nonneg : 0 ≤ (z - (t : ℂ) * Complex.I).re := by
    simpa [Complex.sub_re, Complex.mul_re] using hz_re_nonneg
  have hnorm :
      (z - (t : ℂ) * Complex.I).re ≤
        ‖z - (t : ℂ) * Complex.I‖ :=
    Complex.re_le_norm_of_nonneg_re hdiff_re_nonneg
  have hre :
      (z - (t : ℂ) * Complex.I).re = z.re := by
    simp [Complex.sub_re, Complex.mul_re]
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z - (t : ℂ) * Complex.I‖)
      hre
      hnorm

/-- Factoring `z^2 + t^2` into the two imaginary translates. -/
theorem Complex.add_mul_sub_real_mul_I_eq_sq_add_sq
    (z : ℂ)
    (t : ℝ) :
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I) =
      z ^ 2 + (t : ℂ) ^ 2 := by
  calc
    (z + (t : ℂ) * Complex.I) * (z - (t : ℂ) * Complex.I)
        = z ^ 2 - ((t : ℂ) * Complex.I) ^ 2 := by
          ring
    _ = z ^ 2 + (t : ℂ) ^ 2 := by
          simp [Complex.I_mul_I]

/-- Lower bound for the differentiated Binet denominator from a real-part
margin. -/
theorem Complex.binet_arctan_derivative_denominator_norm_lower
    {z : ℂ}
    {δ t : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hδ_le_re : δ ≤ z.re) :
    δ ^ 2 ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ := by
  have hz_re_nonneg : 0 ≤ z.re :=
    le_trans hδ_nonneg hδ_le_re
  have hplus :
      δ ≤ ‖z + (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_add_real_mul_I hz_re_nonneg t)
  have hminus :
      δ ≤ ‖z - (t : ℂ) * Complex.I‖ :=
    le_trans hδ_le_re
      (Complex.re_le_norm_sub_real_mul_I hz_re_nonneg t)
  have hmul :
      δ * δ ≤
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    mul_le_mul hplus hminus
      hδ_nonneg
      (norm_nonneg (z + (t : ℂ) * Complex.I))
  have hnorm_mul :
      ‖(z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I)‖ =
        ‖z + (t : ℂ) * Complex.I‖ *
          ‖z - (t : ℂ) * Complex.I‖ :=
    norm_mul
      (z + (t : ℂ) * Complex.I)
      (z - (t : ℂ) * Complex.I)
  have hfactor :
      (z + (t : ℂ) * Complex.I) *
          (z - (t : ℂ) * Complex.I) =
        z ^ 2 + (t : ℂ) ^ 2 :=
    Complex.add_mul_sub_real_mul_I_eq_sq_add_sq z t
  have htarget :
      δ * δ ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖ :=
    Eq.subst
      (motive := fun x : ℂ => δ * δ ≤ ‖x‖)
      hfactor
      (Eq.subst
        (motive := fun x : ℝ => δ * δ ≤ x)
        hnorm_mul.symm
        hmul)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z ^ 2 + (t : ℂ) ^ 2‖)
      (sq δ).symm
      htarget

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_I
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w + (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          rw [div_mul_cancel₀ _ hw_ne]
        _ = Complex.I * w := by
          rw [h]
    calc
      w + (t : ℂ) * Complex.I
          = w + (Complex.I * w) * Complex.I := by
            rw [hmul]
      _ = 0 := by
            ring_nf
  exact (Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `-I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_negI
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ -Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w - (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = -Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          rw [div_mul_cancel₀ _ hw_ne]
        _ = -Complex.I * w := by
          rw [h]
    calc
      w - (t : ℂ) * Complex.I
          = w - (-Complex.I * w) * Complex.I := by
            rw [hmul]
      _ = 0 := by
            ring_nf
  exact (Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- The denominator in the Cayley transform defining `Complex.arctan` is
nonzero away from the branch point `-I`. -/
theorem Complex.one_sub_mul_I_ne_zero_of_ne_negI
    {z : ℂ}
    (hz : z ≠ -Complex.I) :
    1 - z * Complex.I ≠ 0 := by
  intro hzero
  have hmul : z * Complex.I = 1 :=
    (sub_eq_zero.mp hzero).symm
  have harg : z = -Complex.I := by
    have hmul' := congrArg (fun u : ℂ => u * (-Complex.I)) hmul
    simpa [mul_assoc, Complex.I_mul_I] using hmul'
  exact hz harg

/-- Imaginary part of the Cayley transform used in the principal-log
definition of complex arctangent. -/
theorem Complex.arctan_cayley_im_eq
    (z : ℂ) :
    ((1 + z * Complex.I) / (1 - z * Complex.I)).im =
      2 * z.re / Complex.normSq (1 - z * Complex.I) := by
  rw [Complex.div_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- For `t > 0` and `0 < w.re`, the Cayley transform appearing in the
principal-log definition of `Complex.arctan ((t : ℂ) / w)` lies in the slit
plane, so the principal logarithm is differentiable there. -/
theorem Complex.binet_arctan_log_argument_mem_slitPlane
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have harg_ne_negI : (t : ℂ) / w ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have hden_ne :
      1 - ((t : ℂ) / w) * Complex.I ≠ 0 :=
    Complex.one_sub_mul_I_ne_zero_of_ne_negI harg_ne_negI
  have hq_im_pos :
      0 <
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) |>.im := by
    have ha_re_pos : 0 < ((t : ℂ) / w).re := by
      rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, zero_div, add_zero]
      exact
        div_pos
          (mul_pos (by exact ht) hw_re_pos)
          (Complex.normSq_pos.mpr hw_ne)
    have hcalc :
        (1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I) |>.im =
          2 * ((t : ℂ) / w).re /
            Complex.normSq (1 - ((t : ℂ) / w) * Complex.I) := by
      exact Complex.arctan_cayley_im_eq ((t : ℂ) / w)
    rw [hcalc]
    exact
      div_pos
        (mul_pos two_pos ha_re_pos)
        (Complex.normSq_pos.mpr hden_ne)
  have hnot_nonpos :
      ¬
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) ≤ 0 := by
    intro hle
    have him_zero :
        (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) |>.im = 0 := by
      exact (Complex.nonpos_iff.mp hle).2
    linarith
  exact (Complex.mem_slitPlane_iff_not_le_zero).2 hnot_nonpos

/-- The rational factor appearing in the Binet arctangent argument has the
expected derivative on the open right half-plane. -/
theorem Complex.binet_arctan_argument_derivative
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => (t : ℂ) / z)
      (-(t : ℂ) / w ^ 2) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_inv hw_ne).const_mul (t : ℂ)

/-- The arctangent derivative needed for the Binet kernel after composing
`Complex.arctan` with `z ↦ (t : ℂ) / z` on the open right half-plane. -/
theorem Complex.arctan_t_div_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
      (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have harg_ne_I : (t : ℂ) / w ≠ Complex.I :=
    Complex.binet_arctan_argument_ne_I hw_re_pos
  have harg_ne_negI : (t : ℂ) / w ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have harg_slit :
      (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane :=
    Complex.binet_arctan_log_argument_mem_slitPlane ht hw_re_pos
  have h_inner :
      HasDerivAt
        (fun z : ℂ => (t : ℂ) / z)
        (-(t : ℂ) / w ^ 2) w := by
    exact Complex.binet_arctan_argument_derivative ht hw_re_pos
  have h_outer :
      HasDerivAt
        Complex.arctan
        ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) ((t : ℂ) / w) := by
    exact
      Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
        harg_ne_I harg_ne_negI harg_slit
  have hcomp :
      HasDerivAt
        (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
        (((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2)) w := by
    simpa [Function.comp_def] using h_outer.comp w h_inner
  have hden_ne : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 :=
    Complex.binet_arctan_derivative_denominator_ne_zero hw_re_pos
  have halg :
      ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2) =
        -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2) := by
    field_simp [hw_ne, hden_ne]
    ring
  exact halg ▸ hcomp

/-- Pointwise derivative of the arctangent kernel in Binet's second-formula
remainder.  This is the branch-sensitive local analytic statement for
`Complex.arctan`, specialized to the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.arctan ((t : ℂ) / z) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Complex.binetSecondFormulaDerivativeKernel t w) w := by
  simpa [Complex.binetSecondFormulaDerivativeKernel] using
    (Complex.arctan_t_div_hasDerivAt ht hw_re_pos).div_const
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- A small ball around a point in the open right half-plane remains in the
open right half-plane. -/
theorem Complex.exists_ball_subset_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z - w‖ < ε → 0 < z.re := by
  refine ⟨w.re / 2, half_pos hw_re_pos, ?_⟩
  intro z hz
  have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa [Complex.norm_eq_abs, sub_re] using
      (abs_re_le_abs (z - w))
  have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
    lt_of_le_of_lt hre_le_norm hz
  have hre_lower : -(w.re / 2) < z.re - w.re :=
    (abs_lt.mp hre_abs_lt).1
  have hw_half_pos : 0 < w.re / 2 :=
    half_pos hw_re_pos
  have hhalf_lt_z : w.re / 2 < z.re := by
    calc
      w.re / 2 = w.re + (-(w.re / 2)) := by ring
      _ < w.re + (z.re - w.re) :=
        add_lt_add_left hre_lower w.re
      _ = z.re := by ring
  exact hw_half_pos.trans hhalf_lt_z

/-- A small ball around a point in the open right half-plane has the explicit
real-part margin `w.re / 2`. -/
theorem Complex.exists_ball_subset_re_ge_half
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z : ℂ, ‖z - w‖ < ε → w.re / 2 ≤ z.re := by
  refine ⟨w.re / 2, half_pos hw_re_pos, ?_⟩
  intro z hz
  have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa [Complex.norm_eq_abs, sub_re] using
      (abs_re_le_abs (z - w))
  have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
    lt_of_le_of_lt hre_le_norm hz
  have hre_lower : -(w.re / 2) < z.re - w.re :=
    (abs_lt.mp hre_abs_lt).1
  have hhalf_lt_z : w.re / 2 < z.re := by
    calc
      w.re / 2 = w.re + (-(w.re / 2)) := by ring
      _ < w.re + (z.re - w.re) :=
        add_lt_add_left hre_lower w.re
      _ = z.re := by ring
  exact le_of_lt hhalf_lt_z

/-- The elementary division rearrangement used by the differentiated Binet
kernel majorant. -/
theorem Real.binet_derivativeKernel_div_sq_div_eq
    {δ d t : ℝ}
    (hδ_sq_ne : δ ^ 2 ≠ 0) :
    (t / δ ^ 2) / d = (1 / δ ^ 2) * (t / d) := by
  field_simp [hδ_sq_ne]
  ring

/-- Norm of the rational factor in the differentiated Binet kernel. -/
theorem Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖-(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2)‖ ≤ t / δ ^ 2 := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  have hδ_nonneg : 0 ≤ δ :=
    le_of_lt hδ_pos
  have hδ_sq_pos : 0 < δ ^ 2 :=
    sq_pos_of_pos hδ_pos
  have hD_lower : δ ^ 2 ≤ ‖D‖ := by
    exact
      Complex.binet_arctan_derivative_denominator_norm_lower
        hδ_nonneg hδ_le_re
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le hδ_sq_pos hD_lower
  have ht_norm : ‖(t : ℂ)‖ = t := by
    calc
      ‖(t : ℂ)‖ = ‖t‖ := by
        simp [Complex.normSq, Real.norm_eq_abs]
      _ = t := Real.norm_of_nonneg (le_of_lt ht)
  have hnorm :
      ‖-(t : ℂ) / D‖ = t / ‖D‖ := by
    calc
      ‖-(t : ℂ) / D‖ = ‖(t : ℂ)‖ / ‖D‖ := by
        rw [norm_div, norm_neg]
      _ = t / ‖D‖ := by
        rw [ht_norm]
  have hdiv :
      t / ‖D‖ ≤ t / δ ^ 2 :=
    div_le_div_of_nonneg_left
      (le_of_lt ht) hδ_sq_pos hD_lower
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ t / δ ^ 2)
      hnorm.symm
      hdiv

/-- Pointwise domination of the differentiated Binet kernel by the real Binet
majorant, with a real-part margin. -/
theorem Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤
      (1 / δ ^ 2) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  let E : ℂ := Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hrational :
      ‖-(t : ℂ) / D‖ ≤ t / δ ^ 2 :=
    Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
      hδ_pos hδ_le_re ht
  have hden_norm : ‖E‖ = d := by
    calc
      ‖E‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
        exact Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = d :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht
  have hd_nonneg : 0 ≤ d :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht)
  have hkernel_norm :
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := by
    calc
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
          ‖(-(t : ℂ) / D) / E‖ := by
        rfl
      _ = ‖-(t : ℂ) / D‖ / ‖E‖ := by
        exact norm_div _ _
      _ = ‖-(t : ℂ) / D‖ / d := by
        rw [hden_norm]
  have hdiv :
      ‖-(t : ℂ) / D‖ / d ≤ (t / δ ^ 2) / d :=
    div_le_div_of_nonneg_right hrational hd_nonneg
  have hδ_sq_ne : δ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hδ_pos)
  have hrearrange :
      (t / δ ^ 2) / d =
        (1 / δ ^ 2) * (t / d) :=
    Real.binet_derivativeKernel_div_sq_div_eq hδ_sq_ne
  calc
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := hkernel_norm
    _ ≤ (t / δ ^ 2) / d := hdiv
    _ = (1 / δ ^ 2) * (t / d) := hrearrange

/-- Local differentiability of the Binet arctangent kernel throughout a ball
inside the open right half-plane, in the form required by mathlib's
parameter-integral differentiation theorem. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∀ z : ℂ,
        ‖z - w‖ < ε →
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  exact
    Complex.binetSecondFormula_arctanKernel_hasDerivAt
      ht (hε_subset z hz)

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases Complex.exists_ball_subset_re_ge_half hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  let δ : ℝ := w.re / 2
  let g : ℝ → ℝ :=
    fun t : ℝ =>
      (1 / δ ^ 2) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
  have hδ_pos : 0 < δ :=
    hε_pos
  have hg_integrable : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    exact
      Real.binetSecondFormula_kernel_majorant_integrableOn.const_mul
        (1 / δ ^ 2)
  refine ⟨ε, hε_pos, g, hg_integrable, ?_⟩
  intro z hz t ht
  have hδ_le_re : δ ≤ z.re :=
    hε_subset z hz
  exact
    Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
      hδ_pos hδ_le_re ht

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  exact
    Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
      hw_re_pos

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, sufficient for differentiating the Binet remainder under
the integral sign near `w` in the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_locally_dominated
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases
    Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
      hw_re_pos with
    ⟨ε, hε_pos, g, hg_int, hg_bound⟩
  refine ⟨ε, hε_pos, g, hg_int, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
	  exact hg_bound z hz t ht

/-- The arctangent kernel and differentiated Binet kernel have the measurability
and base-point integrability needed for dominated differentiation. -/
theorem Complex.binetSecondFormulaRemainder_integral_data
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (∀ᶠ z in 𝓝 w,
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / z) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  sorry

/-- Membership in a smaller ball gives the norm inequality needed for a larger
radius measured in the normed-space coordinates. -/
theorem Complex.norm_sub_lt_of_mem_ball_of_le_radius
    {w z : ℂ}
    {ε η : ℝ}
    (hε_le_η : ε ≤ η)
    (hz : z ∈ Metric.ball w ε) :
    ‖z - w‖ < η := by
  have hdist : dist z w < ε :=
    Metric.mem_ball.mp hz
  have hnorm : ‖z - w‖ < ε := by
    simpa [dist_eq_norm] using hdist
  exact lt_of_lt_of_le hnorm hε_le_η

/-- Uniform-a.e. differentiability of the Binet arctangent kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
          ∀ z : ℂ,
            z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  refine ⟨ε, hε_pos, ?_⟩
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  intro z hz
  have hnorm : ‖z - w‖ < ε := by
    exact
      Complex.norm_sub_lt_of_mem_ball_of_le_radius
        (le_refl ε) hz
  exact
    Complex.binetSecondFormula_arctanKernel_hasDerivAt
      ht (hε_subset z hnorm)

/-- Uniform-a.e. domination of the differentiated Binet kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases
      Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
        hw_re_pos with
    ⟨ε, hε_pos, g, hg_int, hg_bound⟩
  refine ⟨ε, hε_pos, g, hg_int, ?_⟩
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  intro z hz
  have hnorm : ‖z - w‖ < ε := by
    exact
      Complex.norm_sub_lt_of_mem_ball_of_le_radius
        (le_refl ε) hz
  exact hg_bound z hnorm t ht

/-- Dominated-differentiation transport for the Binet remainder once the
measurability and base-point integrability data have been supplied. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
    {w : ℂ}
    {ε : ℝ}
    (hε_pos : 0 < ε)
    (hF_meas :
      ∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF_int :
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    {g : ℝ → ℝ}
    (hg_int :
      Integrable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hbound :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t)
    (hdiff :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  let μ : Measure ℝ := Measure.restrict volume (Set.Ioi (0 : ℝ))
  let F : ℂ → ℝ → ℂ :=
    fun z t =>
      Complex.arctan ((t : ℂ) / z) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let F' : ℂ → ℝ → ℂ :=
    fun z t => Complex.binetSecondFormulaDerivativeKernel t z
  have hmain :
      Integrable (F' w) μ ∧
        HasDerivAt
          (fun z : ℂ => ∫ t, F z t ∂μ)
          (∫ t, F' w t ∂μ) w := by
    exact
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := μ)
        (x₀ := w)
        (F := F)
        (F' := F')
        (bound := g)
        hε_pos
        (by simpa [F, μ] using hF_meas)
        (by simpa [F, μ] using hF_int)
        (by simpa [F', μ] using hF'_meas)
        (by simpa [F', μ] using hbound)
        (by simpa [μ] using hg_int)
        (by simpa [F, F', μ] using hdiff)
  have hscaled :
      HasDerivAt
        (fun z : ℂ => 2 * ∫ t, F z t ∂μ)
        (2 * ∫ t, F' w t ∂μ) w :=
    hmain.2.const_mul 2
  simpa [Complex.binetSecondFormulaRemainder,
    Complex.binetSecondFormulaRemainderDerivative, F, F', μ]
    using hscaled

/-- Integral derivative transport for the Binet second-formula remainder from
the pointwise arctangent-kernel derivative and its local integrable majorant. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
    {w : ℂ}
    (hdata :
      (∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
        Integrable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
        AEStronglyMeasurable
          (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hkernel :
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z)
    (hdominated :
      ∃ ε : ℝ,
        0 < ε ∧
        ∃ g : ℝ → ℝ,
          IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ∀ z : ℂ,
                z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  rcases hdata with ⟨hF_meas, hF_int, hF'_meas⟩
  rcases hkernel with ⟨ε₁, hε₁_pos, hkernel_bound⟩
  rcases hdominated with ⟨ε₂, hε₂_pos, g, hg_int, hdominated_bound⟩
  let ε : ℝ := min ε₁ ε₂
  have hε_pos : 0 < ε :=
    lt_min hε₁_pos hε₂_pos
  have hε_le_ε₁ : ε ≤ ε₁ :=
    min_le_left ε₁ ε₂
  have hε_le_ε₂ : ε ≤ ε₂ :=
    min_le_right ε₁ ε₂
  have hdiff :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z :=
    hkernel_bound.mono
      (fun t ht z hz =>
        ht z
          (Metric.mem_ball.mpr
            (by
              have hnorm :
                  ‖z - w‖ < ε₁ :=
                Complex.norm_sub_lt_of_mem_ball_of_le_radius
                  hε_le_ε₁ hz
              simpa [dist_eq_norm] using hnorm)))
  have hbound :
      ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t :=
    hdominated_bound.mono
      (fun t ht z hz =>
        ht z
          (Metric.mem_ball.mpr
            (by
              have hnorm :
                  ‖z - w‖ < ε₂ :=
                Complex.norm_sub_lt_of_mem_ball_of_le_radius
                  hε_le_ε₂ hz
              simpa [dist_eq_norm] using hnorm)))
  exact
    Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
      hε_pos hF_meas hF_int hF'_meas hg_int hbound hdiff

/-- Differentiation under the integral sign for the Binet second-formula
remainder. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
      (Complex.binetSecondFormulaRemainder_integral_data
        hw_re_pos)
      (Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
        hw_re_pos)
      (Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
        hw_re_pos)

/-- The missing special-function derivative identity behind Binet's second
formula: the logarithmic derivative of Gamma minus the derivative of the
explicit Binet main term is the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  sorry

/-- The logarithmic Gamma side and explicit Binet main term have the
derivative prescribed by the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
      hw_re_pos

/-- The logarithmic Gamma side, after subtracting the explicit Binet main
term, has derivative equal to the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
      hw_re_pos

/-- Differentiating the arctangent-kernel integral under the integral sign
gives the same logarithmic derivative as the Gamma side after subtracting the
explicit Binet main term. -/
theorem Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  have hlog_main :
      HasDerivAt
        (fun z : ℂ =>
          Complex.log (Complex.Gamma z) -
            Complex.binetLogGammaMainTerm z)
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
      hw_re_pos
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  simpa [sub_eq_add_neg, add_assoc] using hlog_main.sub hremainder

/-- A complex function with zero derivative on the open right half-plane is
constant there.  This is the convex-domain mean-value theorem specialized to
the right half-plane. -/
theorem Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
    {F : ℂ → ℂ}
    (hderiv : ∀ {z : ℂ}, 0 < z.re → HasDerivAt F 0 z) :
    ∀ {z w : ℂ}, 0 < z.re → 0 < w.re → F z = F w := by
  intro z w hz hw
  let S : Set ℂ := {u : ℂ | 0 < u.re}
  have hconv : Convex ℝ S := by
    simpa [S] using (convex_halfSpace_re_gt (r := 0))
  have hopen : IsOpen S := by
    simpa [S] using
      (isOpen_lt continuous_const Complex.continuous_re :
        IsOpen {u : ℂ | (0 : ℝ) < u.re})
  have hdiff : DifferentiableOn ℂ F S := by
    intro u hu
    exact (hderiv hu).differentiableAt.differentiableWithinAt
  have hzero :
      ∀ u ∈ S, fderivWithin ℂ F S u = 0 := by
    intro u hu
    have hunique : UniqueDiffWithinAt ℂ S u :=
      hopen.uniqueDiffWithinAt hu
    exact
      (hderiv hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin hunique
  exact hconv.is_const_of_fderivWithin_eq_zero hdiff hzero hz hw

/-- The two sides of Binet's second formula have the same complex derivative
on the open right half-plane.

This is the analytic continuation/differentiation root: after differentiating
the arctangent-kernel integral under the integral sign, the derivative agrees
with the logarithmic derivative of `Gamma` minus the derivative of the explicit
main term. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  exact
    Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
      hw_re_pos

/-- A holomorphic Binet difference with zero derivative on the open right
half-plane is determined there by its positive-real values. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
    (hreal :
      ∀ {x : ℝ},
        0 < x →
          Complex.log (Complex.Gamma (x : ℂ)) =
            Complex.binetLogGammaMainTerm (x : ℂ) +
              Complex.binetSecondFormulaRemainder (x : ℂ))
    (hderiv :
      ∀ {w : ℂ},
        0 < w.re →
          HasDerivAt
            (fun z : ℂ =>
              Complex.log (Complex.Gamma z) -
                (Complex.binetLogGammaMainTerm z +
                  Complex.binetSecondFormulaRemainder z))
            0 w) :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  intro w hw
  let F : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.log (Complex.Gamma z) -
        (Complex.binetLogGammaMainTerm z +
          Complex.binetSecondFormulaRemainder z)
  have hbase_re : 0 < (w.re : ℂ).re := by
    simpa using hw
  have hconstant : F (w.re : ℂ) = F w :=
    Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
      (F := F)
      (fun hz => hderiv hz)
      hbase_re hw
  have hbase_zero : F (w.re : ℂ) = 0 := by
    dsimp [F]
    exact sub_eq_zero.mpr (hreal hw)
  have hw_zero : F w = 0 := by
    exact Eq.trans hconstant.symm hbase_zero
  exact sub_eq_zero.mp hw_zero

/-- The open right half-plane is connected to the positive real axis by
paths along which the principal-log Binet difference has zero derivative.

This consumes the real-axis normalization and the zero-derivative identity to
propagate Binet's formula through the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
      (fun hx =>
        Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
          hx)
      (fun hw_re_pos =>
        Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
          hw_re_pos)

/-- The classical second Binet integral representation, with the principal
logarithm normalization used by `Complex.binetLogGammaMainTerm` and the
literal arctangent-kernel remainder used in this package. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_principalLog :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative

/-- Binet's logarithmic identity follows from the classical second Binet
integral representation on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_principalLog

/-- Binet's second logarithmic formula on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation

/-- The literal arctangent-kernel Binet formula is an open-right-half-plane
statement.  On the boundary `w = i y`, the kernel crosses the principal
arctangent branch point at `t = y`, so this theorem records the large-radius
form for the existing pointwise integral only on `0 < w.re`. -/
theorem Complex.Gamma_binetSecondFormula_large_openRightHalfPlane :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro w hw_re_pos _hR
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane
      w hw_re_pos

/-- Large-radius Binet formula for the existing principal-arctangent integral.
The hypothesis is open half-plane because the current remainder is the
pointwise kernel integral, not a boundary-value object on the imaginary axis. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_large_openRightHalfPlane

/-- Closed-sector continuation of Binet's second logarithmic formula after a
large-radius cutoff for the literal open-half-plane arctangent remainder. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation

/-- Binet's second logarithmic formula for Gamma in the open right half-plane,
away from the origin and after a fixed large-radius cutoff. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.arctan_series_term_norm_le_geometric
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ ≤
        ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
  intro n
  have hz_nonneg : 0 ≤ ‖z‖ :=
    norm_nonneg z
  have hsq_le_half : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    have hsq_le_quarter : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      sq_le_sq' hz_nonneg hz
    have hquarter_le_half : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) := by
      norm_num
    exact le_trans hsq_le_quarter hquarter_le_half
  have hpow_bound :
      ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
    calc
      ‖z‖ ^ (2 * n + 1) = ‖z‖ * (‖z‖ ^ 2) ^ n := by
        ring
      _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
        exact
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sq_nonneg ‖z‖) hsq_le_half n)
            hz_nonneg
  have hden_ge_one : (1 : ℝ) ≤ ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
    norm_num
  have hden_pos : 0 < ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one hden_ge_one
  have hdiv_le :
      ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ ≤
        ‖z‖ ^ (2 * n + 1) := by
    exact
      div_le_of_le_mul₀
        (norm_nonneg _)
        hden_pos
        (by
          calc
            ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ ^ (2 * n + 1) * 1 := by
              rw [mul_one]
            _ ≤ ‖z‖ ^ (2 * n + 1) * ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hden_ge_one
                (pow_nonneg hz_nonneg (2 * n + 1)))
  calc
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ =
        ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      simp [norm_div, norm_mul, norm_pow]
    _ ≤ ‖z‖ ^ (2 * n + 1) := hdiv_le
    _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := hpow_bound

/-- The geometric majorant for the arctangent series sums to `2 * ‖z‖`. -/
theorem Complex.arctan_geometric_majorant_hasSum
    (z : ℂ) :
    HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) := by
  have hgeom :
      HasSum (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hmul :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n))
        (‖z‖ * (1 - (1 / 2 : ℝ))⁻¹) :=
    hgeom.mul_left ‖z‖
  have hsum_eq :
      ‖z‖ * (1 - (1 / 2 : ℝ))⁻¹ = 2 * ‖z‖ := by
    ring
  exact hsum_eq ▸ hmul

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`, proved from the arctangent power series. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  have hz_lt_one : ‖z‖ < (1 : ℝ) :=
    lt_of_le_of_lt hz (by norm_num : (1 / 2 : ℝ) < 1)
  have hseries :
      HasSum
        (fun n : ℕ =>
          (-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ))
        (Complex.arctan z) :=
    Complex.hasSum_arctan hz_lt_one
  have hmajorant :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) :=
    Complex.arctan_geometric_majorant_hasSum z
  exact
    hseries.norm_le_of_bounded hmajorant
      (Complex.arctan_series_term_norm_le_geometric hz)

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  exact
    Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series hz

/-- Norm of the Binet arctangent argument. -/
theorem Complex.norm_real_div_eq_real_norm_div
    (t : ℝ)
    (w : ℂ) :
    ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ := by
  calc
    ‖(t : ℂ) / w‖ = ‖(t : ℂ)‖ / ‖w‖ := by
      exact norm_div _ _
    _ = ‖t‖ / ‖w‖ := by
      rw [Complex.normSq, Real.norm_eq_abs]

/-- On the lower split interval `0 < t ≤ ‖w‖ / 2`, the Binet arctangent
argument lies in the half disk. -/
theorem Complex.binetSecondFormula_small_interval_argument_norm_le_half
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have ht_norm : ‖t‖ = t :=
    Real.norm_of_nonneg (le_of_lt ht.1)
  have harg_norm :
      ‖(t : ℂ) / w‖ = t / ‖w‖ := by
    calc
      ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ :=
        Complex.norm_real_div_eq_real_norm_div t w
      _ = t / ‖w‖ := by
        rw [ht_norm]
  have hdiv_le : t / ‖w‖ ≤ (1 / 2 : ℝ) := by
    exact (div_le_iff₀ hw_norm_pos).mpr ht.2
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 / 2 : ℝ))
      harg_norm.symm
      hdiv_le

/-- Small-argument arctangent bound for the Binet kernel.

The principal arctangent has branch singularities at `±I`, so the honest
pointwise estimate is a small-argument sector estimate, not a global
open-half-plane estimate. -/
theorem Complex.binetSecondFormula_arctan_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
        ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * (t / ‖w‖) := by
  intro t ht hsmall
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * ‖(t : ℂ) / w‖ :=
    Complex.norm_arctan_le_two_norm_of_norm_le_half hsmall
  have ht_norm : ‖t‖ = t :=
    Real.norm_of_nonneg (le_of_lt ht)
  have harg_norm :
      ‖(t : ℂ) / w‖ = t / ‖w‖ := by
    calc
      ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ :=
        Complex.norm_real_div_eq_real_norm_div t w
      _ = t / ‖w‖ := by
        rw [ht_norm]
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * x)
      harg_norm
      harctan

/-- Local division of the arctangent estimate by the positive Binet
denominator. -/
theorem Complex.binetSecondFormula_kernel_norm_le_of_small_argument
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : 0 < t)
    (hsmall : ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 * (t / ‖w‖)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * (t / ‖w‖) :=
    Complex.binetSecondFormula_arctan_norm_le hw_re_pos t ht hsmall
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht)
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ = ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      rw [hden_norm]
    _ ≤ (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg

/-- Local small-interval pointwise kernel estimate for the lower split piece. -/
theorem Complex.binetSecondFormula_kernel_norm_le_on_small_interval
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 * (t / ‖w‖)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      hw_re_pos ht.1
      (Complex.binetSecondFormula_small_interval_argument_norm_le_half
        hw_re_pos ht)

/-- Division of the arctangent estimate by the positive Binet denominator. -/
theorem Complex.binetSecondFormula_kernel_norm_le_of_arctan_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      hw_re_pos ht (hsmall t ht)

/-- Small-argument pointwise kernel estimate for Binet's second-formula
remainder. -/
theorem Complex.binetSecondFormula_kernel_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_arctan_norm_le hw_re_pos hsmall

/-- Small-argument sector form of the Binet-kernel estimate on the open right
half-plane.

The literal closed-boundary principal-arctangent kernel has singular boundary
values on the imaginary axis, so the pointwise owner estimate stays in the
open half-plane and away from the arctangent branch singularities.  Closed
sector estimates are obtained later by the continued Binet remainder, not by
evaluating this kernel pointwise on the boundary. -/
theorem Complex.binetSecondFormula_kernel_norm_le_openRightHalfPlaneSector
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact Complex.binetSecondFormula_kernel_norm_le hw_re_pos hsmall

end

end LFunctions
end Boundary
