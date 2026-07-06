import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part30

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology NNReal

namespace ZetaAdmissibleFunction

/-- Real coordinate normalization for a real point with an added real imaginary offset. -/
theorem ofReal_add_realAdd_mul_I_re (x y z : ℝ) :
    (x + (y + z) * Complex.I : ℂ).re = x := by
  have hcoef : (((y : ℂ) + (z : ℂ)) = ((y + z : ℝ) : ℂ)) :=
    (Complex.ofReal_add y z).symm
  calc
    (x + (y + z) * Complex.I : ℂ).re =
        (x + ((y + z : ℝ) : ℂ) * Complex.I : ℂ).re := by
      exact congrArg Complex.re
        (congrArg (fun w : ℂ => (x : ℂ) + w * Complex.I) hcoef)
    _ = x := by
      exact ofReal_add_mul_I_re x (y + z)

/-- Imaginary coordinate normalization for a real point with an added real imaginary offset. -/
theorem ofReal_add_realAdd_mul_I_im (x y z : ℝ) :
    (x + (y + z) * Complex.I : ℂ).im = y + z := by
  have hcoef : (((y : ℂ) + (z : ℂ)) = ((y + z : ℝ) : ℂ)) :=
    (Complex.ofReal_add y z).symm
  calc
    (x + (y + z) * Complex.I : ℂ).im =
        (x + ((y + z : ℝ) : ℂ) * Complex.I : ℂ).im := by
      exact congrArg Complex.im
        (congrArg (fun w : ℂ => (x : ℂ) + w * Complex.I) hcoef)
    _ = y + z := by
      exact ofReal_add_mul_I_im x (y + z)

/-- Real coordinate normalization for a real point with a subtracted real imaginary offset. -/
theorem ofReal_add_realSub_mul_I_re (x y z : ℝ) :
    (x + (y - z) * Complex.I : ℂ).re = x := by
  have hcoef : (((y : ℂ) - (z : ℂ)) = ((y - z : ℝ) : ℂ)) :=
    (Complex.ofReal_sub y z).symm
  calc
    (x + (y - z) * Complex.I : ℂ).re =
        (x + ((y - z : ℝ) : ℂ) * Complex.I : ℂ).re := by
      exact congrArg Complex.re
        (congrArg (fun w : ℂ => (x : ℂ) + w * Complex.I) hcoef)
    _ = x := by
      exact ofReal_add_mul_I_re x (y - z)

/-- Imaginary coordinate normalization for a real point with a subtracted real imaginary offset. -/
theorem ofReal_add_realSub_mul_I_im (x y z : ℝ) :
    (x + (y - z) * Complex.I : ℂ).im = y - z := by
  have hcoef : (((y : ℂ) - (z : ℂ)) = ((y - z : ℝ) : ℂ)) :=
    (Complex.ofReal_sub y z).symm
  calc
    (x + (y - z) * Complex.I : ℂ).im =
        (x + ((y - z : ℝ) : ℂ) * Complex.I : ℂ).im := by
      exact congrArg Complex.im
        (congrArg (fun w : ℂ => (x : ℂ) + w * Complex.I) hcoef)
    _ = y - z := by
      exact ofReal_add_mul_I_im x (y - z)

/-- Positive-radius normalized arctangent-kernel value.  This is the scalar form consumed by
the bottom-side inverse-kernel computation after factoring
`(t - Ri)⁻¹ = (t + Ri) / (t² + R²)`. -/
theorem finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div_normalized
    {R : ℝ} (hR : 0 < R) :
    R⁻¹ * (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) = Real.pi / 2 := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hscale :
      (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
        R • (Real.pi / 2) :=
    finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div_eq hR
  calc
    R⁻¹ * (∫ t : ℝ in (-R)..R, (1 + (t / R) ^ 2)⁻¹) =
        R⁻¹ * (R • (Real.pi / 2)) := by
      exact congrArg (fun x : ℝ => R⁻¹ * x) hscale
    _ = R⁻¹ * (R * (Real.pi / 2)) := by
      exact congrArg (fun x : ℝ => R⁻¹ * x) (Algebra.id.smul_eq_mul R (Real.pi / 2))
    _ = (R⁻¹ * R) * (Real.pi / 2) := by
      exact (mul_assoc R⁻¹ R (Real.pi / 2)).symm
    _ = 1 * (Real.pi / 2) := by
      exact congrArg (fun x : ℝ => x * (Real.pi / 2)) (inv_mul_cancel₀ hR_ne)
    _ = Real.pi / 2 := by
      exact one_mul (Real.pi / 2)

/-- Symmetric-interval cancellation for an odd integrand.  This isolates the real-part
cancellation in the square inverse-kernel side computations. -/
theorem finiteRectangle_integral_odd_neg_pos_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (R : ℝ)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    (∫ x : ℝ in (-R)..R, f x) = 0 := by
  let I : E := ∫ x : ℝ in (-R)..R, f x
  have hcomp :
      (∫ x : ℝ in (-R)..R, f (-x)) = I := by
    have hraw :
        (∫ x : ℝ in (-R)..R, f (-x)) =
          ∫ x : ℝ in -R..-(-R), f x :=
      intervalIntegral.integral_comp_neg (f := f)
    have hright :
        (∫ x : ℝ in -R..-(-R), f x) = I := by
      calc
        (∫ x : ℝ in -R..-(-R), f x) =
            ∫ x : ℝ in -R..R, f x := by
          exact congrArg (fun u : ℝ => ∫ x : ℝ in -R..u, f x) (neg_neg R)
        _ = I := by
          exact Eq.refl _
    exact Eq.trans hraw hright
  have hpoint :
      (∫ x : ℝ in (-R)..R, f (-x)) =
        ∫ x : ℝ in (-R)..R, -f x :=
    intervalIntegral.integral_congr
      (fun x _ => hodd x)
  have hneg :
      (∫ x : ℝ in (-R)..R, -f x) = -I := by
    exact intervalIntegral.integral_neg
  have hI_neg : I = -I := by
    exact (Eq.trans hcomp.symm (Eq.trans hpoint hneg))
  have hzero_sum : I + I = 0 := by
    calc
      I + I = I + -I := by
        exact congrArg (fun z : E => I + z) hI_neg
      _ = 0 := by
        exact add_neg_cancel I
  have htwo :
      (2 : ℝ) • I = 0 := by
    calc
      (2 : ℝ) • I = I + I := by
        exact two_smul ℝ I
      _ = 0 := by
        exact hzero_sum
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  exact (smul_eq_zero.mp htwo).resolve_left htwo_ne

/-- Real part commutes with a finite interval integral of a complex-valued function. -/
theorem finiteRectangle_intervalIntegral_re
    {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ x : ℝ in a..b, f x).re =
      ∫ x : ℝ in a..b, (f x).re := by
  have hmap :
      (∫ x : ℝ in a..b, Complex.reCLM (f x)) =
        Complex.reCLM (∫ x : ℝ in a..b, f x) :=
    ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hf
  have hleft :
      (∫ x : ℝ in a..b, Complex.reCLM (f x)) =
        ∫ x : ℝ in a..b, (f x).re :=
    intervalIntegral.integral_congr
      (fun x _ => Complex.reCLM_apply (f x))
  have hright :
      Complex.reCLM (∫ x : ℝ in a..b, f x) =
        (∫ x : ℝ in a..b, f x).re :=
    Complex.reCLM_apply (∫ x : ℝ in a..b, f x)
  exact Eq.trans hright.symm (Eq.trans hmap.symm hleft)

/-- Imaginary part commutes with a finite interval integral of a complex-valued function. -/
theorem finiteRectangle_intervalIntegral_im
    {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ x : ℝ in a..b, f x).im =
      ∫ x : ℝ in a..b, (f x).im := by
  have hmap :
      (∫ x : ℝ in a..b, Complex.imCLM (f x)) =
        Complex.imCLM (∫ x : ℝ in a..b, f x) :=
    ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hf
  have hleft :
      (∫ x : ℝ in a..b, Complex.imCLM (f x)) =
        ∫ x : ℝ in a..b, (f x).im :=
    intervalIntegral.integral_congr
      (fun x _ => Complex.imCLM_apply (f x))
  have hright :
      Complex.imCLM (∫ x : ℝ in a..b, f x) =
        (∫ x : ℝ in a..b, f x).im :=
    Complex.imCLM_apply (∫ x : ℝ in a..b, f x)
  exact Eq.trans hright.symm (Eq.trans hmap.symm hleft)

/-- Scalar algebra for the square inverse-kernel imaginary part. -/
theorem finiteRectangleSquareSubInv_im_kernel_eq_scaled_arctanKernel
    {R : ℝ} (hR : 0 < R) (t : ℝ) :
    R / (t ^ 2 + R ^ 2) =
      R⁻¹ * (1 + (t / R) ^ 2)⁻¹ := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hR2_ne : R ^ 2 ≠ 0 :=
    pow_ne_zero 2 hR_ne
  have hden :
      1 + (t / R) ^ 2 = (t ^ 2 + R ^ 2) / R ^ 2 := by
    calc
      1 + (t / R) ^ 2 =
          R ^ 2 / R ^ 2 + (t / R) ^ 2 := by
        exact congrArg (fun x : ℝ => x + (t / R) ^ 2) (div_self hR2_ne).symm
      _ = R ^ 2 / R ^ 2 + t ^ 2 / R ^ 2 := by
        exact congrArg (fun x : ℝ => R ^ 2 / R ^ 2 + x)
          (div_pow t R 2)
      _ = (R ^ 2 + t ^ 2) / R ^ 2 := by
        exact (add_div (R ^ 2) (t ^ 2) (R ^ 2)).symm
      _ = (t ^ 2 + R ^ 2) / R ^ 2 := by
        exact congrArg (fun x : ℝ => x / R ^ 2) (add_comm (R ^ 2) (t ^ 2))
  have htarget_ne : t ^ 2 + R ^ 2 ≠ 0 := by
    have hR2_pos : 0 < R ^ 2 :=
      sq_pos_of_ne_zero hR_ne
    have hsum_pos : 0 < t ^ 2 + R ^ 2 :=
      lt_of_lt_of_le hR2_pos (le_add_of_nonneg_left (sq_nonneg t))
    exact ne_of_gt hsum_pos
  have hinv :
      (1 + (t / R) ^ 2)⁻¹ =
        R ^ 2 / (t ^ 2 + R ^ 2) := by
    calc
      (1 + (t / R) ^ 2)⁻¹ =
          ((t ^ 2 + R ^ 2) / R ^ 2)⁻¹ := by
        exact congrArg Inv.inv hden
      _ = (R ^ 2) / (t ^ 2 + R ^ 2) := by
        exact inv_div (t ^ 2 + R ^ 2) (R ^ 2)
  calc
    R / (t ^ 2 + R ^ 2) =
        R⁻¹ * (R ^ 2 / (t ^ 2 + R ^ 2)) := by
      calc
        R / (t ^ 2 + R ^ 2) =
            (R⁻¹ * R ^ 2) / (t ^ 2 + R ^ 2) := by
          have hRmul : R⁻¹ * R ^ 2 = R := by
            calc
              R⁻¹ * R ^ 2 = R⁻¹ * (R * R) := by
                exact congrArg (fun x : ℝ => R⁻¹ * x) (sq R)
              _ = (R⁻¹ * R) * R := by
                exact (mul_assoc R⁻¹ R R).symm
              _ = 1 * R := by
                exact congrArg (fun x : ℝ => x * R) (inv_mul_cancel₀ hR_ne)
              _ = R := by
                exact one_mul R
          exact congrArg (fun x : ℝ => x / (t ^ 2 + R ^ 2)) hRmul.symm
        _ = R⁻¹ * (R ^ 2 / (t ^ 2 + R ^ 2)) := by
          exact mul_div_assoc R⁻¹ (R ^ 2) (t ^ 2 + R ^ 2)
    _ = R⁻¹ * (1 + (t / R) ^ 2)⁻¹ := by
      exact congrArg (fun x : ℝ => R⁻¹ * x) hinv.symm

/-- Real coordinate of the inverse of `x + yi`. -/
theorem finiteRectangleSquareSubInv_coordinate_inv_re
    (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹).re =
      x / (x ^ 2 + y ^ 2) := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hre : z.re = x :=
    ofReal_add_mul_I_re x y
  have hnorm : Complex.normSq z = x ^ 2 + y ^ 2 :=
    Complex.normSq_add_mul_I x y
  calc
    (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹).re = z⁻¹.re := by
      exact Eq.refl _
    _ = z.re / Complex.normSq z := by
      exact Complex.inv_re z
    _ = x / Complex.normSq z := by
      exact congrArg (fun u : ℝ => u / Complex.normSq z) hre
    _ = x / (x ^ 2 + y ^ 2) := by
      exact congrArg (fun u : ℝ => x / u) hnorm

/-- Imaginary coordinate of the inverse of `x + yi`. -/
theorem finiteRectangleSquareSubInv_coordinate_inv_im
    (x y : ℝ) :
    (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹).im =
      -y / (x ^ 2 + y ^ 2) := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have him : z.im = y :=
    ofReal_add_mul_I_im x y
  have hnorm : Complex.normSq z = x ^ 2 + y ^ 2 :=
    Complex.normSq_add_mul_I x y
  calc
    (((x : ℂ) + (y : ℂ) * Complex.I)⁻¹).im = z⁻¹.im := by
      exact Eq.refl _
    _ = -z.im / Complex.normSq z := by
      exact Complex.inv_im z
    _ = -y / Complex.normSq z := by
      exact congrArg (fun u : ℝ => -u / Complex.normSq z) him
    _ = -y / (x ^ 2 + y ^ 2) := by
      exact congrArg (fun u : ℝ => -y / u) hnorm

/-- Bottom centered inverse-kernel real coordinate. -/
theorem finiteRectangleSquareSubInv_bottomCentered_inv_re
    (R t : ℝ) :
    (((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).re =
      t / (t ^ 2 + R ^ 2) := by
  have hcoord :
      (((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).re =
        t / (t ^ 2 + (-R) ^ 2) :=
    finiteRectangleSquareSubInv_coordinate_inv_re t (-R)
  have hden : t ^ 2 + (-R) ^ 2 = t ^ 2 + R ^ 2 := by
    exact congrArg (fun u : ℝ => t ^ 2 + u) (neg_sq R)
  exact
    Eq.trans hcoord
      (congrArg (fun u : ℝ => t / u) hden)

/-- Bottom centered inverse-kernel imaginary coordinate. -/
theorem finiteRectangleSquareSubInv_bottomCentered_inv_im
    (R t : ℝ) :
    (((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).im =
      R / (t ^ 2 + R ^ 2) := by
  have hcoord :
      (((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).im =
        -(-R) / (t ^ 2 + (-R) ^ 2) :=
    finiteRectangleSquareSubInv_coordinate_inv_im t (-R)
  have hnum : -(-R) = R :=
    neg_neg R
  have hden : t ^ 2 + (-R) ^ 2 = t ^ 2 + R ^ 2 := by
    exact congrArg (fun u : ℝ => t ^ 2 + u) (neg_sq R)
  calc
    (((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).im =
        -(-R) / (t ^ 2 + (-R) ^ 2) := hcoord
    _ = R / (t ^ 2 + (-R) ^ 2) := by
      exact congrArg (fun u : ℝ => u / (t ^ 2 + (-R) ^ 2)) hnum
    _ = R / (t ^ 2 + R ^ 2) := by
      exact congrArg (fun u : ℝ => R / u) hden

/-- Top centered inverse-kernel real coordinate. -/
theorem finiteRectangleSquareSubInv_topCentered_inv_re
    (R t : ℝ) :
    (((t : ℂ) + (R : ℂ) * Complex.I)⁻¹).re =
      t / (t ^ 2 + R ^ 2) :=
  finiteRectangleSquareSubInv_coordinate_inv_re t R

/-- Top centered inverse-kernel imaginary coordinate. -/
theorem finiteRectangleSquareSubInv_topCentered_inv_im
    (R t : ℝ) :
    (((t : ℂ) + (R : ℂ) * Complex.I)⁻¹).im =
      -R / (t ^ 2 + R ^ 2) :=
  finiteRectangleSquareSubInv_coordinate_inv_im t R

/-- Right centered inverse-kernel real coordinate. -/
theorem finiteRectangleSquareSubInv_rightCentered_inv_re
    (R t : ℝ) :
    (((R : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
      R / (R ^ 2 + t ^ 2) :=
  finiteRectangleSquareSubInv_coordinate_inv_re R t

/-- Right centered inverse-kernel imaginary coordinate. -/
theorem finiteRectangleSquareSubInv_rightCentered_inv_im
    (R t : ℝ) :
    (((R : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
      -t / (R ^ 2 + t ^ 2) :=
  finiteRectangleSquareSubInv_coordinate_inv_im R t

/-- Left centered inverse-kernel real coordinate. -/
theorem finiteRectangleSquareSubInv_leftCentered_inv_re
    (R t : ℝ) :
    ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
      -R / (R ^ 2 + t ^ 2) := by
  have hcoord :
      ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
        (-R) / ((-R) ^ 2 + t ^ 2) :=
    finiteRectangleSquareSubInv_coordinate_inv_re (-R) t
  have hden : (-R) ^ 2 + t ^ 2 = R ^ 2 + t ^ 2 := by
    exact congrArg (fun u : ℝ => u + t ^ 2) (neg_sq R)
  exact
    Eq.trans hcoord
      (congrArg (fun u : ℝ => -R / u) hden)

/-- Left centered inverse-kernel imaginary coordinate. -/
theorem finiteRectangleSquareSubInv_leftCentered_inv_im
    (R t : ℝ) :
    ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
      -t / (R ^ 2 + t ^ 2) := by
  have hcoord :
      ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
        -t / ((-R) ^ 2 + t ^ 2) :=
    finiteRectangleSquareSubInv_coordinate_inv_im (-R) t
  have hden : (-R) ^ 2 + t ^ 2 = R ^ 2 + t ^ 2 := by
    exact congrArg (fun u : ℝ => u + t ^ 2) (neg_sq R)
  exact
    Eq.trans hcoord
      (congrArg (fun u : ℝ => -t / u) hden)

/-- Real-part interval reduction for a centered horizontal inverse-kernel side. -/
theorem finiteRectangleSquareSubInv_horizontalCentered_integral_re
    {R Y : ℝ}
    (hf :
      IntervalIntegrable
        (fun t : ℝ => ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹)
        volume (-R) R) :
    (∫ t : ℝ in (-R)..R, ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).re =
      ∫ t : ℝ in (-R)..R, t / (t ^ 2 + Y ^ 2) := by
  have hre :
      (∫ t : ℝ in (-R)..R, ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).re =
        ∫ t : ℝ in (-R)..R,
          (((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).re :=
    finiteRectangle_intervalIntegral_re hf
  have hpoint :
      (∫ t : ℝ in (-R)..R,
          (((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).re) =
        ∫ t : ℝ in (-R)..R, t / (t ^ 2 + Y ^ 2) :=
    intervalIntegral.integral_congr
      (fun t _ => finiteRectangleSquareSubInv_coordinate_inv_re t Y)
  exact Eq.trans hre hpoint

/-- Imaginary-part interval reduction for a centered horizontal inverse-kernel side. -/
theorem finiteRectangleSquareSubInv_horizontalCentered_integral_im
    {R Y : ℝ}
    (hf :
      IntervalIntegrable
        (fun t : ℝ => ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹)
        volume (-R) R) :
    (∫ t : ℝ in (-R)..R, ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).im =
      ∫ t : ℝ in (-R)..R, -Y / (t ^ 2 + Y ^ 2) := by
  have him :
      (∫ t : ℝ in (-R)..R, ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).im =
        ∫ t : ℝ in (-R)..R,
          (((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).im :=
    finiteRectangle_intervalIntegral_im hf
  have hpoint :
      (∫ t : ℝ in (-R)..R,
          (((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹).im) =
        ∫ t : ℝ in (-R)..R, -Y / (t ^ 2 + Y ^ 2) :=
    intervalIntegral.integral_congr
      (fun t _ => finiteRectangleSquareSubInv_coordinate_inv_im t Y)
  exact Eq.trans him hpoint

/-- Real-part interval reduction for a centered vertical inverse-kernel side. -/
theorem finiteRectangleSquareSubInv_verticalCentered_integral_re
    {R X : ℝ}
    (hf :
      IntervalIntegrable
        (fun t : ℝ => ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        volume (-R) R) :
    (∫ t : ℝ in (-R)..R, ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
      ∫ t : ℝ in (-R)..R, X / (X ^ 2 + t ^ 2) := by
  have hre :
      (∫ t : ℝ in (-R)..R, ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
        ∫ t : ℝ in (-R)..R,
          (((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).re :=
    finiteRectangle_intervalIntegral_re hf
  have hpoint :
      (∫ t : ℝ in (-R)..R,
          (((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).re) =
        ∫ t : ℝ in (-R)..R, X / (X ^ 2 + t ^ 2) :=
    intervalIntegral.integral_congr
      (fun t _ => finiteRectangleSquareSubInv_coordinate_inv_re X t)
  exact Eq.trans hre hpoint

/-- Imaginary-part interval reduction for a centered vertical inverse-kernel side. -/
theorem finiteRectangleSquareSubInv_verticalCentered_integral_im
    {R X : ℝ}
    (hf :
      IntervalIntegrable
        (fun t : ℝ => ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        volume (-R) R) :
    (∫ t : ℝ in (-R)..R, ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
      ∫ t : ℝ in (-R)..R, -t / (X ^ 2 + t ^ 2) := by
  have him :
      (∫ t : ℝ in (-R)..R, ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
        ∫ t : ℝ in (-R)..R,
          (((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).im :=
    finiteRectangle_intervalIntegral_im hf
  have hpoint :
      (∫ t : ℝ in (-R)..R,
          (((X : ℂ) + (t : ℂ) * Complex.I)⁻¹).im) =
        ∫ t : ℝ in (-R)..R, -t / (X ^ 2 + t ^ 2) :=
    intervalIntegral.integral_congr
      (fun t _ => finiteRectangleSquareSubInv_coordinate_inv_im X t)
  exact Eq.trans him hpoint

/-- The top side of the inverse-kernel square boundary, translated to the universal
centered top side. -/
theorem finiteRectangleSquareSubInvTopIntegral_eq_centered
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareSubInvTopIntegral a R =
      ∫ t : ℝ in (-R)..R, ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹ := by
  let h : ℝ → ℂ :=
    fun x : ℝ => (((x : ℂ) + (((a.im + R : ℝ) : ℂ)) * Complex.I) - a)⁻¹
  have hleft : a.re - R = -R + a.re := by
    calc
      a.re - R = a.re + -R := by
        exact sub_eq_add_neg a.re R
      _ = -R + a.re := by
        exact add_comm a.re (-R)
  have hright : a.re + R = R + a.re := by
    exact add_comm a.re R
  have htranslated :
      (∫ t : ℝ in (-R)..R, h (t + a.re)) =
        ∫ x : ℝ in (-R + a.re)..(R + a.re), h x :=
    intervalIntegral.integral_comp_add_right h a.re
  have hendpoints :
      (∫ x : ℝ in (a.re - R)..(a.re + R), h x) =
        ∫ x : ℝ in (-R + a.re)..(R + a.re), h x :=
    congrArg₂ (fun left right : ℝ => ∫ x : ℝ in left..right, h x) hleft hright
  have hpointwise :
      ∀ t : ℝ,
        (((t + a.re : ℝ) : ℂ) + (((a.im + R : ℝ) : ℂ)) * Complex.I) - a =
          (t : ℂ) + (R : ℂ) * Complex.I := by
    intro t
    have hbase :=
      finiteRectangleSquareSubInvTop_point_sub_center a R (t + a.re)
    have hx : (t + a.re) - a.re = t := by
      exact add_sub_cancel_right t a.re
    have hy : (a.im + R) - a.im = R := by
      exact add_sub_cancel_left a.im R
    exact
      Eq.trans hbase
        (Complex.ext
          (by
            calc
              (((((t + a.re) - a.re : ℝ) : ℂ) +
                  (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).re) =
                  ((t + a.re) - a.re) := by
                exact ofReal_add_mul_I_re ((t + a.re) - a.re)
                  ((a.im + R) - a.im)
              _ = t := by
                exact hx
              _ = ((t : ℂ) + (R : ℂ) * Complex.I).re := by
                exact (ofReal_add_mul_I_re t R).symm)
          (by
            calc
              (((((t + a.re) - a.re : ℝ) : ℂ) +
                  (((a.im + R) - a.im : ℝ) : ℂ) * Complex.I).im) =
                  ((a.im + R) - a.im) := by
                exact ofReal_add_mul_I_im ((t + a.re) - a.re)
                  ((a.im + R) - a.im)
              _ = R := by
                exact hy
              _ = ((t : ℂ) + (R : ℂ) * Complex.I).im := by
                exact (ofReal_add_mul_I_im t R).symm))
  have hpoint :
      (∫ t : ℝ in (-R)..R, h (t + a.re)) =
        ∫ t : ℝ in (-R)..R, ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr
      (fun t _ => congrArg Inv.inv (hpointwise t))
  calc
    finiteRectangleSquareSubInvTopIntegral a R =
        ∫ x : ℝ in (a.re - R)..(a.re + R), h x := by
      exact Eq.refl _
    _ = ∫ x : ℝ in (-R + a.re)..(R + a.re), h x := by
      exact hendpoints
    _ = ∫ t : ℝ in (-R)..R, h (t + a.re) := by
      exact htranslated.symm
    _ = ∫ t : ℝ in (-R)..R, ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹ := by
      exact hpoint

/-- The right side of the inverse-kernel square boundary, translated to the universal
centered right side. -/
theorem finiteRectangleSquareSubInvRightIntegral_eq_centered
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareSubInvRightIntegral a R =
      ∫ t : ℝ in (-R)..R, ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
  let h : ℝ → ℂ :=
    fun y : ℝ => ((((a.re + R : ℝ) : ℂ) + y * Complex.I) - a)⁻¹
  have hleft : a.im - R = -R + a.im := by
    calc
      a.im - R = a.im + -R := by
        exact sub_eq_add_neg a.im R
      _ = -R + a.im := by
        exact add_comm a.im (-R)
  have hright : a.im + R = R + a.im := by
    exact add_comm a.im R
  have htranslated :
      (∫ t : ℝ in (-R)..R, h (t + a.im)) =
        ∫ y : ℝ in (-R + a.im)..(R + a.im), h y :=
    intervalIntegral.integral_comp_add_right h a.im
  have hendpoints :
      (∫ y : ℝ in (a.im - R)..(a.im + R), h y) =
        ∫ y : ℝ in (-R + a.im)..(R + a.im), h y :=
    congrArg₂ (fun left right : ℝ => ∫ y : ℝ in left..right, h y) hleft hright
  have hpointwise :
      ∀ t : ℝ,
        (((a.re + R : ℝ) : ℂ) + (((t + a.im : ℝ) : ℂ)) * Complex.I - a) =
          (R : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    have hbase :=
      finiteRectangleSquareSubInvRight_point_sub_center a R (t + a.im)
    have hx : (a.re + R) - a.re = R := by
      exact add_sub_cancel_left a.re R
    have hy : (t + a.im) - a.im = t := by
      exact add_sub_cancel_right t a.im
    exact
      Eq.trans hbase
        (Complex.ext
          (by
            calc
              (((((a.re + R) - a.re : ℝ) : ℂ) +
                  (((t + a.im) - a.im : ℝ) : ℂ) * Complex.I).re) =
                  ((a.re + R) - a.re) := by
                exact ofReal_add_mul_I_re ((a.re + R) - a.re)
                  ((t + a.im) - a.im)
              _ = R := by
                exact hx
              _ = ((R : ℂ) + (t : ℂ) * Complex.I).re := by
                exact (ofReal_add_mul_I_re R t).symm)
          (by
            calc
              (((((a.re + R) - a.re : ℝ) : ℂ) +
                  (((t + a.im) - a.im : ℝ) : ℂ) * Complex.I).im) =
                  ((t + a.im) - a.im) := by
                exact ofReal_add_mul_I_im ((a.re + R) - a.re)
                  ((t + a.im) - a.im)
              _ = t := by
                exact hy
              _ = ((R : ℂ) + (t : ℂ) * Complex.I).im := by
                exact (ofReal_add_mul_I_im R t).symm))
  have hpoint :
      (∫ t : ℝ in (-R)..R, h (t + a.im)) =
        ∫ t : ℝ in (-R)..R, ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr
      (fun t _ => congrArg Inv.inv (hpointwise t))
  calc
    finiteRectangleSquareSubInvRightIntegral a R =
        ∫ y : ℝ in (a.im - R)..(a.im + R), h y := by
      exact Eq.refl _
    _ = ∫ y : ℝ in (-R + a.im)..(R + a.im), h y := by
      exact hendpoints
    _ = ∫ t : ℝ in (-R)..R, h (t + a.im) := by
      exact htranslated.symm
    _ = ∫ t : ℝ in (-R)..R, ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
      exact hpoint

/-- The left side of the inverse-kernel square boundary, translated to the universal
centered left side. -/
theorem finiteRectangleSquareSubInvLeftIntegral_eq_centered
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareSubInvLeftIntegral a R =
      ∫ t : ℝ in (-R)..R, (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
  let h : ℝ → ℂ :=
    fun y : ℝ => ((((a.re - R : ℝ) : ℂ) + y * Complex.I) - a)⁻¹
  have hleft : a.im - R = -R + a.im := by
    calc
      a.im - R = a.im + -R := by
        exact sub_eq_add_neg a.im R
      _ = -R + a.im := by
        exact add_comm a.im (-R)
  have hright : a.im + R = R + a.im := by
    exact add_comm a.im R
  have htranslated :
      (∫ t : ℝ in (-R)..R, h (t + a.im)) =
        ∫ y : ℝ in (-R + a.im)..(R + a.im), h y :=
    intervalIntegral.integral_comp_add_right h a.im
  have hendpoints :
      (∫ y : ℝ in (a.im - R)..(a.im + R), h y) =
        ∫ y : ℝ in (-R + a.im)..(R + a.im), h y :=
    congrArg₂ (fun left right : ℝ => ∫ y : ℝ in left..right, h y) hleft hright
  have hpointwise :
      ∀ t : ℝ,
        (((a.re - R : ℝ) : ℂ) + (((t + a.im : ℝ) : ℂ)) * Complex.I - a) =
          ((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    intro t
    have hbase :=
      finiteRectangleSquareSubInvLeft_point_sub_center a R (t + a.im)
    have hx : (a.re - R) - a.re = -R := by
      calc
        (a.re - R) - a.re = (a.re + -R) - a.re := by
          exact congrArg (fun z : ℝ => z - a.re) (sub_eq_add_neg a.re R)
        _ = -R := by
          exact add_sub_cancel_left a.re (-R)
    have hy : (t + a.im) - a.im = t := by
      exact add_sub_cancel_right t a.im
    exact
      Eq.trans hbase
        (Complex.ext
          (by
            calc
              (((((a.re - R) - a.re : ℝ) : ℂ) +
                  (((t + a.im) - a.im : ℝ) : ℂ) * Complex.I).re) =
                  ((a.re - R) - a.re) := by
                exact ofReal_add_mul_I_re ((a.re - R) - a.re)
                  ((t + a.im) - a.im)
              _ = -R := by
                exact hx
              _ = (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
                exact (ofReal_add_mul_I_re (-R) t).symm)
          (by
            calc
              (((((a.re - R) - a.re : ℝ) : ℂ) +
                  (((t + a.im) - a.im : ℝ) : ℂ) * Complex.I).im) =
                  ((t + a.im) - a.im) := by
                exact ofReal_add_mul_I_im ((a.re - R) - a.re)
                  ((t + a.im) - a.im)
              _ = t := by
                exact hy
              _ = (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I).im := by
                exact (ofReal_add_mul_I_im (-R) t).symm))
  have hpoint :
      (∫ t : ℝ in (-R)..R, h (t + a.im)) =
        ∫ t : ℝ in (-R)..R, ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹) :=
    intervalIntegral.integral_congr
      (fun t _ => congrArg Inv.inv (hpointwise t))
  calc
    finiteRectangleSquareSubInvLeftIntegral a R =
        ∫ y : ℝ in (a.im - R)..(a.im + R), h y := by
      exact Eq.refl _
    _ = ∫ y : ℝ in (-R + a.im)..(R + a.im), h y := by
      exact hendpoints
    _ = ∫ t : ℝ in (-R)..R, h (t + a.im) := by
      exact htranslated.symm
    _ = ∫ t : ℝ in (-R)..R, ((((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
      exact hpoint

/-- Bottom centered side normalized to the `x + yi` coordinate form. -/
theorem finiteRectangleSquareSubInvBottomIntegral_eq_centered_add_neg
    (a : ℂ) (R : ℝ) :
    finiteRectangleSquareSubInvBottomIntegral a R =
      ∫ t : ℝ in (-R)..R, ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹ := by
  have hcenter :
      finiteRectangleSquareSubInvBottomIntegral a R =
        ∫ t : ℝ in (-R)..R, ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ :=
    finiteRectangleSquareSubInvBottomIntegral_eq_centered a R
  have hpoint :
      (∫ t : ℝ in (-R)..R, ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) =
        ∫ t : ℝ in (-R)..R, ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr
      (fun t _ =>
        congrArg Inv.inv
          (by
            calc
              (t : ℂ) - (R : ℂ) * Complex.I =
                  (t : ℂ) + -((R : ℂ) * Complex.I) := by
                exact sub_eq_add_neg (t : ℂ) ((R : ℂ) * Complex.I)
              _ = (t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I := by
                exact congrArg (fun z : ℂ => (t : ℂ) + z)
                  (by
                    calc
                      -((R : ℂ) * Complex.I) = (-(R : ℂ)) * Complex.I := by
                        exact (neg_mul (R : ℂ) Complex.I).symm
                      _ = ((-R : ℝ) : ℂ) * Complex.I := by
                        exact congrArg (fun z : ℂ => z * Complex.I)
                          (Complex.ofReal_neg R).symm)))
  exact Eq.trans hcenter hpoint

/-- A horizontal centered inverse-kernel with nonzero height is interval-integrable. -/
theorem finiteRectangleSquareSubInv_horizontalCentered_intervalIntegrable
    (R Y : ℝ) (hY : Y ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ => ((t : ℂ) + (Y : ℂ) * Complex.I)⁻¹)
      volume (-R) R := by
  have hbase :
      Continuous fun t : ℝ => (t : ℂ) + (Y : ℂ) * Complex.I :=
    continuous_ofReal.add continuous_const
  have hnonzero :
      ∀ t : ℝ, (t : ℂ) + (Y : ℂ) * Complex.I ≠ 0 := by
    intro t hzero
    have him :
        ((t : ℂ) + (Y : ℂ) * Complex.I).im = (0 : ℂ).im :=
      congrArg Complex.im hzero
    have hY_zero : Y = 0 :=
      Eq.trans (ofReal_add_mul_I_im t Y).symm him
    exact hY hY_zero
  exact (hbase.inv₀ hnonzero).intervalIntegrable (-R) R

/-- A vertical centered inverse-kernel with nonzero abscissa is interval-integrable. -/
theorem finiteRectangleSquareSubInv_verticalCentered_intervalIntegrable
    (R X : ℝ) (hX : X ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ => ((X : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      volume (-R) R := by
  have hbase :
      Continuous fun t : ℝ => (X : ℂ) + (t : ℂ) * Complex.I :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hnonzero :
      ∀ t : ℝ, (X : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t hzero
    have hre :
        ((X : ℂ) + (t : ℂ) * Complex.I).re = (0 : ℂ).re :=
      congrArg Complex.re hzero
    have hX_zero : X = 0 :=
      Eq.trans (ofReal_add_mul_I_re X t).symm hre
    exact hX hX_zero
  exact (hbase.inv₀ hnonzero).intervalIntegrable (-R) R

/-- Odd cancellation for the real coordinate of the centered horizontal inverse kernel. -/
theorem finiteRectangleSquareSubInv_horizontal_re_integral_eq_zero
    (R Y : ℝ) :
    (∫ t : ℝ in (-R)..R, t / (t ^ 2 + Y ^ 2)) = 0 := by
  exact finiteRectangle_integral_odd_neg_pos_eq_zero
    (fun t : ℝ => t / (t ^ 2 + Y ^ 2)) R
    (fun t : ℝ =>
      calc
        (-t) / ((-t) ^ 2 + Y ^ 2) =
            (-t) / (t ^ 2 + Y ^ 2) := by
          exact congrArg (fun u : ℝ => (-t) / (u + Y ^ 2)) (neg_sq t)
        _ = -(t / (t ^ 2 + Y ^ 2)) := by
          exact neg_div (t ^ 2 + Y ^ 2) t)

/-- Odd cancellation for the imaginary coordinate of the centered vertical inverse kernel. -/
theorem finiteRectangleSquareSubInv_vertical_im_integral_eq_zero
    (R X : ℝ) :
    (∫ t : ℝ in (-R)..R, -t / (X ^ 2 + t ^ 2)) = 0 := by
  exact finiteRectangle_integral_odd_neg_pos_eq_zero
    (fun t : ℝ => -t / (X ^ 2 + t ^ 2)) R
    (fun t : ℝ =>
      calc
        -(-t) / (X ^ 2 + (-t) ^ 2) =
            t / (X ^ 2 + (-t) ^ 2) := by
          exact congrArg (fun u : ℝ => u / (X ^ 2 + (-t) ^ 2)) (neg_neg t)
        _ = t / (X ^ 2 + t ^ 2) := by
          exact congrArg (fun u : ℝ => t / (X ^ 2 + u)) (neg_sq t)
        _ = -(-(t / (X ^ 2 + t ^ 2))) := by
          exact (neg_neg (t / (X ^ 2 + t ^ 2))).symm
        _ = -(-t / (X ^ 2 + t ^ 2)) := by
          exact congrArg Neg.neg (neg_div (X ^ 2 + t ^ 2) t).symm)

/-- Positive centered arctangent-kernel integral. -/
theorem finiteRectangleSquareSubInv_positive_kernel_integral_eq_halfPi
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, R / (t ^ 2 + R ^ 2)) = Real.pi / 2 := by
  let g : ℝ → ℝ := fun t : ℝ => (1 + (t / R) ^ 2)⁻¹
  have hpoint :
      (∫ t : ℝ in (-R)..R, R / (t ^ 2 + R ^ 2)) =
        ∫ t : ℝ in (-R)..R, R⁻¹ * g t :=
    intervalIntegral.integral_congr
      (fun t _ => finiteRectangleSquareSubInv_im_kernel_eq_scaled_arctanKernel hR t)
  have hconst :
      (∫ t : ℝ in (-R)..R, R⁻¹ * g t) =
        R⁻¹ * ∫ t : ℝ in (-R)..R, g t :=
    intervalIntegral.integral_const_mul R⁻¹ g
  exact Eq.trans hpoint
    (Eq.trans hconst
      (finiteRectangleSquareSubInv_arctanKernel_scaled_comp_div_normalized hR))

/-- Negative centered arctangent-kernel integral. -/
theorem finiteRectangleSquareSubInv_negative_kernel_integral_eq_negHalfPi
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, -R / (t ^ 2 + R ^ 2)) = -(Real.pi / 2) := by
  have hneg :
      (∫ t : ℝ in (-R)..R, -R / (t ^ 2 + R ^ 2)) =
        ∫ t : ℝ in (-R)..R, -(R / (t ^ 2 + R ^ 2)) :=
    intervalIntegral.integral_congr
      (fun t _ => neg_div (t ^ 2 + R ^ 2) R)
  have hint :
      (∫ t : ℝ in (-R)..R, -(R / (t ^ 2 + R ^ 2))) =
        -(∫ t : ℝ in (-R)..R, R / (t ^ 2 + R ^ 2)) :=
    intervalIntegral.integral_neg
  exact Eq.trans hneg
    (Eq.trans hint
      (congrArg Neg.neg
        (finiteRectangleSquareSubInv_positive_kernel_integral_eq_halfPi hR)))

/-- The centered bottom inverse-kernel side integral is `(π/2)i`. -/
theorem finiteRectangleSquareSubInv_bottomCentered_integral_eq_halfPiI
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hnegR_ne : (-R) ≠ 0 :=
    neg_ne_zero.mpr hR_ne
  have hf :
      IntervalIntegrable
        (fun t : ℝ => ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹)
        volume (-R) R :=
    finiteRectangleSquareSubInv_horizontalCentered_intervalIntegrable R (-R) hnegR_ne
  exact Complex.ext
    (calc
      (∫ t : ℝ in (-R)..R,
          ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).re =
          ∫ t : ℝ in (-R)..R, t / (t ^ 2 + (-R) ^ 2) := by
        exact finiteRectangleSquareSubInv_horizontalCentered_integral_re hf
      _ = ∫ t : ℝ in (-R)..R, t / (t ^ 2 + R ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ => congrArg (fun u : ℝ => t / (t ^ 2 + u)) (neg_sq R))
      _ = 0 := by
        exact finiteRectangleSquareSubInv_horizontal_re_integral_eq_zero R R
      _ = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).re := by
        calc
          0 = -(((Real.pi / 2 : ℝ) : ℂ).im) := by
            exact Eq.trans (neg_zero : -(0 : ℝ) = 0).symm
              (congrArg Neg.neg (ofReal_im (Real.pi / 2)).symm)
          _ = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).re := by
            exact (mul_I_re ((Real.pi / 2 : ℝ) : ℂ)).symm)
    (calc
      (∫ t : ℝ in (-R)..R,
          ((t : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)⁻¹).im =
          ∫ t : ℝ in (-R)..R, -(-R) / (t ^ 2 + (-R) ^ 2) := by
        exact finiteRectangleSquareSubInv_horizontalCentered_integral_im hf
      _ = ∫ t : ℝ in (-R)..R, R / (t ^ 2 + R ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ =>
            calc
              -(-R) / (t ^ 2 + (-R) ^ 2) =
                  R / (t ^ 2 + (-R) ^ 2) := by
                exact congrArg (fun u : ℝ => u / (t ^ 2 + (-R) ^ 2)) (neg_neg R)
              _ = R / (t ^ 2 + R ^ 2) := by
                exact congrArg (fun u : ℝ => R / (t ^ 2 + u)) (neg_sq R))
      _ = Real.pi / 2 := by
        exact finiteRectangleSquareSubInv_positive_kernel_integral_eq_halfPi hR
      _ = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im := by
        calc
          Real.pi / 2 = ((Real.pi / 2 : ℝ) : ℂ).re := by
            exact (ofReal_re (Real.pi / 2)).symm
          _ = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im := by
            exact (mul_I_im ((Real.pi / 2 : ℝ) : ℂ)).symm)

/-- The centered top inverse-kernel side integral is `-(π/2)i`. -/
theorem finiteRectangleSquareSubInv_topCentered_integral_eq_negHalfPiI
    {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in (-R)..R, ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) =
      -((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hf :
      IntervalIntegrable
        (fun t : ℝ => ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹)
        volume (-R) R :=
    finiteRectangleSquareSubInv_horizontalCentered_intervalIntegrable R R hR_ne
  exact Complex.ext
    (calc
      (∫ t : ℝ in (-R)..R,
          ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹).re =
          ∫ t : ℝ in (-R)..R, t / (t ^ 2 + R ^ 2) := by
        exact finiteRectangleSquareSubInv_horizontalCentered_integral_re hf
      _ = 0 := by
        exact finiteRectangleSquareSubInv_horizontal_re_integral_eq_zero R R
      _ = (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I).re := by
        calc
          0 = -0 := by
            exact (neg_zero : -(0 : ℝ) = 0).symm
          _ = -((-((Real.pi / 2 : ℝ) : ℂ)).im) := by
            have hneg_im :
                (-((Real.pi / 2 : ℝ) : ℂ)).im = 0 := by
              calc
                (-((Real.pi / 2 : ℝ) : ℂ)).im =
                    ((-(Real.pi / 2) : ℝ) : ℂ).im := by
                  exact congrArg Complex.im (Complex.ofReal_neg (Real.pi / 2)).symm
                _ = 0 := by
                  exact ofReal_im (-(Real.pi / 2))
            exact congrArg Neg.neg hneg_im.symm
          _ = (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I).re := by
            exact (mul_I_re (-((Real.pi / 2 : ℝ) : ℂ))).symm)
    (calc
      (∫ t : ℝ in (-R)..R,
          ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹).im =
          ∫ t : ℝ in (-R)..R, -R / (t ^ 2 + R ^ 2) := by
        exact finiteRectangleSquareSubInv_horizontalCentered_integral_im hf
      _ = -(Real.pi / 2) := by
        exact finiteRectangleSquareSubInv_negative_kernel_integral_eq_negHalfPi hR
      _ = (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im := by
        calc
          -(Real.pi / 2) = (-((Real.pi / 2 : ℝ) : ℂ)).re := by
            calc
              -(Real.pi / 2) = ((-(Real.pi / 2) : ℝ) : ℂ).re := by
                exact (ofReal_re (-(Real.pi / 2))).symm
              _ = (-((Real.pi / 2 : ℝ) : ℂ)).re := by
                exact congrArg Complex.re (Complex.ofReal_neg (Real.pi / 2))
          _ = (-((Real.pi / 2 : ℝ) : ℂ) * Complex.I).im := by
            exact (mul_I_im (-((Real.pi / 2 : ℝ) : ℂ))).symm)

/-- Multiplication by `i` sends a real complex number to the corresponding imaginary one. -/
theorem finiteRectangleSquareSubInv_I_smul_of_re_im
    {z : ℂ} {x : ℝ} (hre : z.re = x) (him : z.im = 0) :
    Complex.I • z = (x : ℂ) * Complex.I := by
  have hz : z = (x : ℂ) := by
    exact Complex.ext
      (Eq.trans hre (ofReal_re x).symm)
      (Eq.trans him (ofReal_im x).symm)
  calc
    Complex.I • z = Complex.I • (x : ℂ) := by
      exact congrArg (fun w : ℂ => Complex.I • w) hz
    _ = Complex.I * (x : ℂ) := by
      exact Eq.refl _
    _ = (x : ℂ) * Complex.I := by
      exact mul_comm Complex.I (x : ℂ)

/-- `i` times the centered right inverse-kernel side integral is `(π/2)i`. -/
theorem finiteRectangleSquareSubInv_rightCentered_smul_eq_halfPiI
    {R : ℝ} (hR : 0 < R) :
    Complex.I •
        (∫ t : ℝ in (-R)..R, ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hf :
      IntervalIntegrable
        (fun t : ℝ => ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        volume (-R) R :=
    finiteRectangleSquareSubInv_verticalCentered_intervalIntegrable R R hR_ne
  exact finiteRectangleSquareSubInv_I_smul_of_re_im
    (calc
      (∫ t : ℝ in (-R)..R,
          ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
          ∫ t : ℝ in (-R)..R, R / (R ^ 2 + t ^ 2) := by
        exact finiteRectangleSquareSubInv_verticalCentered_integral_re hf
      _ = ∫ t : ℝ in (-R)..R, R / (t ^ 2 + R ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ => congrArg (fun u : ℝ => R / u) (add_comm (R ^ 2) (t ^ 2)))
      _ = Real.pi / 2 := by
        exact finiteRectangleSquareSubInv_positive_kernel_integral_eq_halfPi hR)
    (calc
      (∫ t : ℝ in (-R)..R,
          ((R : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
          ∫ t : ℝ in (-R)..R, -t / (R ^ 2 + t ^ 2) := by
        exact finiteRectangleSquareSubInv_verticalCentered_integral_im hf
      _ = 0 := by
        exact finiteRectangleSquareSubInv_vertical_im_integral_eq_zero R R)

/-- `i` times the centered left inverse-kernel side integral is `-(π/2)i`. -/
theorem finiteRectangleSquareSubInv_leftCentered_smul_eq_negHalfPiI
    {R : ℝ} (hR : 0 < R) :
    Complex.I •
        (∫ t : ℝ in (-R)..R, (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR
  have hnegR_ne : (-R) ≠ 0 :=
    neg_ne_zero.mpr hR_ne
  have hf :
      IntervalIntegrable
        (fun t : ℝ => (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        volume (-R) R :=
    finiteRectangleSquareSubInv_verticalCentered_intervalIntegrable R (-R) hnegR_ne
  exact finiteRectangleSquareSubInv_I_smul_of_re_im
    (calc
      (∫ t : ℝ in (-R)..R,
          (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).re =
          ∫ t : ℝ in (-R)..R, (-R) / ((-R) ^ 2 + t ^ 2) := by
        exact finiteRectangleSquareSubInv_verticalCentered_integral_re hf
      _ = ∫ t : ℝ in (-R)..R, -R / (R ^ 2 + t ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ => congrArg (fun u : ℝ => -R / (u + t ^ 2)) (neg_sq R))
      _ = ∫ t : ℝ in (-R)..R, -R / (t ^ 2 + R ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ => congrArg (fun u : ℝ => -R / u) (add_comm (R ^ 2) (t ^ 2)))
      _ = -(Real.pi / 2) := by
        exact finiteRectangleSquareSubInv_negative_kernel_integral_eq_negHalfPi hR)
    (calc
      (∫ t : ℝ in (-R)..R,
          (((-R : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹).im =
          ∫ t : ℝ in (-R)..R, -t / ((-R) ^ 2 + t ^ 2) := by
        exact finiteRectangleSquareSubInv_verticalCentered_integral_im hf
      _ = ∫ t : ℝ in (-R)..R, -t / (R ^ 2 + t ^ 2) := by
        exact intervalIntegral.integral_congr
          (fun t _ => congrArg (fun u : ℝ => -t / (u + t ^ 2)) (neg_sq R))
      _ = 0 := by
        exact finiteRectangleSquareSubInv_vertical_im_integral_eq_zero R R)

/-- Sub-sink (bottom side value): the inverse-kernel integral along the bottom side of the
square is `(π/2)·i`.  After `finiteRectangleSquareSubInvBottomIntegral_eq_centered` (`Part10`)
this is `∫_{-R}^{R} (t - Ri)⁻¹ dt`, whose value is the principal-branch logarithm difference
`Log(R - Ri) - Log(-R - Ri) = i(−π/4) − i(−3π/4) = (π/2)·i`, the path staying off the
negative-real branch cut since its imaginary part is `−R < 0`. -/
theorem finiteRectangleSquareSubInvBottomIntegral_eq_halfPiI
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareSubInvBottomIntegral c R = (Real.pi / 2 : ℂ) * Complex.I := by
  exact Eq.trans (finiteRectangleSquareSubInvBottomIntegral_eq_centered_add_neg c R)
    (Eq.trans
      (finiteRectangleSquareSubInv_bottomCentered_integral_eq_halfPiI hR)
      (congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_div Real.pi 2)))

/-- Sub-sink (top side value): the inverse-kernel integral along the top side is `−(π/2)·i`. -/
theorem finiteRectangleSquareSubInvTopIntegral_eq_negHalfPiI
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareSubInvTopIntegral c R = -(Real.pi / 2 : ℂ) * Complex.I := by
  exact Eq.trans (finiteRectangleSquareSubInvTopIntegral_eq_centered c R)
    (Eq.trans
      (finiteRectangleSquareSubInv_topCentered_integral_eq_negHalfPiI hR)
      (congrArg (fun z : ℂ => -z * Complex.I) (Complex.ofReal_div Real.pi 2)))

/-- Sub-sink (right side value): `i` times the inverse-kernel integral along the right side is
`(π/2)·i`. -/
theorem finiteRectangleSquareSubInvRightIntegral_smul_eq_halfPiI
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Complex.I • finiteRectangleSquareSubInvRightIntegral c R = (Real.pi / 2 : ℂ) * Complex.I := by
  exact Eq.trans
    (congrArg (fun z : ℂ => Complex.I • z)
      (finiteRectangleSquareSubInvRightIntegral_eq_centered c R))
    (Eq.trans
      (finiteRectangleSquareSubInv_rightCentered_smul_eq_halfPiI hR)
      (congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_div Real.pi 2)))

/-- Sub-sink (left side value): `i` times the inverse-kernel integral along the left side is
`−(π/2)·i`. -/
theorem finiteRectangleSquareSubInvLeftIntegral_smul_eq_negHalfPiI
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Complex.I • finiteRectangleSquareSubInvLeftIntegral c R = -(Real.pi / 2 : ℂ) * Complex.I := by
  exact Eq.trans
    (congrArg (fun z : ℂ => Complex.I • z)
      (finiteRectangleSquareSubInvLeftIntegral_eq_centered c R))
    (Eq.trans
      (finiteRectangleSquareSubInv_leftCentered_smul_eq_negHalfPiI hR)
      (calc
        ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I =
            -(((Real.pi / 2 : ℝ) : ℂ)) * Complex.I := by
          exact congrArg (fun z : ℂ => z * Complex.I) (Complex.ofReal_neg (Real.pi / 2))
        _ = -(Real.pi / 2 : ℂ) * Complex.I := by
          exact congrArg (fun z : ℂ => -z * Complex.I) (Complex.ofReal_div Real.pi 2)))

/-- Sink (model computation leaf): the square boundary integral of the simple-pole kernel
`(z - c)⁻¹` around its centre is `2πi`.

This is the rectangular analogue of `circleIntegral.integral_sub_inv_of_mem_ball`: it is the
square-contour winding number `1`.

Thin wrapper: a pure term-mode application of
`finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_sideValues` (`Part09`) to the four
named side-value sub-sinks. -/
theorem finiteRectangleSquareBoundaryIntegral_inv_eq_twoPiI
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R =
      (2 * ↑Real.pi * Complex.I : ℂ) :=
  finiteRectangleSquareBoundaryIntegral_sub_inv_eq_twoPiI_of_sideValues c R
    (finiteRectangleSquareSubInvBottomIntegral_eq_halfPiI c hR)
    (finiteRectangleSquareSubInvTopIntegral_eq_negHalfPiI c hR)
    (finiteRectangleSquareSubInvRightIntegral_smul_eq_halfPiI c hR)
    (finiteRectangleSquareSubInvLeftIntegral_smul_eq_negHalfPiI c hR)

/-- Sub-sink (homogeneity): the square boundary integral is `ℂ`-homogeneous in the integrand.
Each of the four oriented side integrals is homogeneous by `intervalIntegral.integral_smul`. -/
theorem finiteRectangleSquareBoundaryIntegral_smul
    (c : ℂ) (R : ℝ) (r : ℂ) (v : ℂ → ℂ) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => r • v z) c R =
      r • finiteRectangleSquareBoundaryIntegral v c R := by
  let bottom : ℂ :=
    ∫ x : ℝ in (c.re - R)..(c.re + R),
      v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))
  let top : ℂ :=
    ∫ x : ℝ in (c.re - R)..(c.re + R),
      v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))
  let right : ℂ :=
    ∫ y : ℝ in (c.im - R)..(c.im + R),
      v (((c.re + R : ℝ) : ℂ) + y * Complex.I)
  let left : ℂ :=
    ∫ y : ℝ in (c.im - R)..(c.im + R),
      v (((c.re - R : ℝ) : ℂ) + y * Complex.I)
  have hbottom :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          r • v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) =
        r • bottom :=
    intervalIntegral.integral_smul r
      (fun x : ℝ => v (x + (((c.im - R : ℝ) : ℂ) * Complex.I)))
  have htop :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          r • v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) =
        r • top :=
    intervalIntegral.integral_smul r
      (fun x : ℝ => v (x + (((c.im + R : ℝ) : ℂ) * Complex.I)))
  have hright :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) =
        r • right :=
    intervalIntegral.integral_smul r
      (fun y : ℝ => v (((c.re + R : ℝ) : ℂ) + y * Complex.I))
  have hleft :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) =
        r • left :=
    intervalIntegral.integral_smul r
      (fun y : ℝ => v (((c.re - R : ℝ) : ℂ) + y * Complex.I))
  have halgebra :
      r • (bottom - top + Complex.I • right - Complex.I • left) =
        r • bottom - r • top + Complex.I • (r • right) -
          Complex.I • (r • left) := by
    calc
      r • (bottom - top + Complex.I • right - Complex.I • left) =
          r • (bottom - top + Complex.I • right) - r • (Complex.I • left) := by
        exact smul_sub r (bottom - top + Complex.I • right) (Complex.I • left)
      _ =
          (r • (bottom - top) + r • (Complex.I • right)) -
            r • (Complex.I • left) := by
        exact congrArg (fun x : ℂ => x - r • (Complex.I • left))
          (smul_add r (bottom - top) (Complex.I • right))
      _ =
          ((r • bottom - r • top) + r • (Complex.I • right)) -
            r • (Complex.I • left) := by
        exact congrArg
          (fun x : ℂ => (x + r • (Complex.I • right)) - r • (Complex.I • left))
          (smul_sub r bottom top)
      _ =
          ((r • bottom - r • top) + Complex.I • (r • right)) -
            r • (Complex.I • left) := by
        exact congrArg
          (fun x : ℂ => ((r • bottom - r • top) + x) - r • (Complex.I • left))
          (calc
            r • (Complex.I • right) = (r * Complex.I) • right := by
              exact smul_smul r Complex.I right
            _ = (Complex.I * r) • right := by
              exact congrArg (fun x : ℂ => x • right) (mul_comm r Complex.I)
            _ = Complex.I • (r • right) := by
              exact (smul_smul Complex.I r right).symm)
      _ =
          ((r • bottom - r • top) + Complex.I • (r • right)) -
            Complex.I • (r • left) := by
        exact congrArg
          (fun x : ℂ => ((r • bottom - r • top) + Complex.I • (r • right)) - x)
          (calc
            r • (Complex.I • left) = (r * Complex.I) • left := by
              exact smul_smul r Complex.I left
            _ = (Complex.I * r) • left := by
              exact congrArg (fun x : ℂ => x • left) (mul_comm r Complex.I)
            _ = Complex.I • (r • left) := by
              exact (smul_smul Complex.I r left).symm)
      _ =
          r • bottom - r • top + Complex.I • (r • right) -
            Complex.I • (r • left) := by
        exact Eq.refl _
  calc
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => r • v z) c R =
        (∫ x : ℝ in (c.re - R)..(c.re + R),
          r • v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in (c.re - R)..(c.re + R),
            r • v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in (c.im - R)..(c.im + R),
                r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) := by
      exact finiteRectangleSquareBoundaryIntegral_eq (fun z : ℂ => r • v z) c R
    _ =
        r • bottom - r • top + Complex.I • (r • right) -
          Complex.I • (r • left) := by
      have hhorizontal :
          (∫ x : ℝ in (c.re - R)..(c.re + R),
            r • v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) -
            (∫ x : ℝ in (c.re - R)..(c.re + R),
              r • v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) +
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in (c.im - R)..(c.im + R),
                    r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) =
            r • bottom - r • top +
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) :=
        congrArg₂
          (fun x y : ℂ =>
            x - y +
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)))
          hbottom htop
      have hvertical :
          r • bottom - r • top +
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  r • v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) =
            r • bottom - r • top + Complex.I • (r • right) -
              Complex.I • (r • left) :=
        congrArg₂
          (fun x y : ℂ =>
            r • bottom - r • top + Complex.I • x - Complex.I • y)
          hright hleft
      exact Eq.trans hhorizontal hvertical
    _ =
        r • (bottom - top + Complex.I • right - Complex.I • left) := by
      exact halgebra.symm
    _ = r • finiteRectangleSquareBoundaryIntegral v c R := by
      exact congrArg (fun z : ℂ => r • z)
        (finiteRectangleSquareBoundaryIntegral_eq v c R).symm

/-- The bottom side of a positive-radius centered square avoids its centre. -/
theorem finiteRectangleSquareBottomSide_ne_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    x + (((c.im - R : ℝ) : ℂ) * Complex.I) ≠ c := by
  intro h
  have him_eq :
      (x + (((c.im - R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im :=
    congrArg Complex.im h
  have him_left :
      (x + (((c.im - R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im - R :=
    ofReal_add_mul_I_im x (c.im - R)
  have hsub :
      c.im - R = c.im :=
    Eq.trans him_left.symm him_eq
  have hzero :
      R = 0 := by
    calc
      R = c.im - (c.im - R) := by
        exact (sub_sub_self c.im R).symm
      _ = c.im - c.im := by
        exact congrArg (fun y : ℝ => c.im - y) hsub
      _ = 0 := by
        exact sub_self c.im
  exact (ne_of_gt hR) hzero

/-- The top side of a positive-radius centered square avoids its centre. -/
theorem finiteRectangleSquareTopSide_ne_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    x + (((c.im + R : ℝ) : ℂ) * Complex.I) ≠ c := by
  intro h
  have him_eq :
      (x + (((c.im + R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im :=
    congrArg Complex.im h
  have him_left :
      (x + (((c.im + R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im + R :=
    ofReal_add_mul_I_im x (c.im + R)
  have hadd :
      c.im + R = c.im :=
    Eq.trans him_left.symm him_eq
  have hzero :
      R = 0 := by
    calc
      R = (c.im + R) - c.im := by
        exact (add_sub_cancel_left c.im R).symm
      _ = c.im - c.im := by
        exact congrArg (fun y : ℝ => y - c.im) hadd
      _ = 0 := by
        exact sub_self c.im
  exact (ne_of_gt hR) hzero

/-- The right side of a positive-radius centered square avoids its centre. -/
theorem finiteRectangleSquareRightSide_ne_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (y : ℝ) :
    ((c.re + R : ℝ) : ℂ) + y * Complex.I ≠ c := by
  intro h
  have hre_eq :
      (((c.re + R : ℝ) : ℂ) + y * Complex.I).re = c.re :=
    congrArg Complex.re h
  have hre_left :
      (((c.re + R : ℝ) : ℂ) + y * Complex.I).re = c.re + R :=
    ofReal_add_mul_I_re (c.re + R) y
  have hadd :
      c.re + R = c.re :=
    Eq.trans hre_left.symm hre_eq
  have hzero :
      R = 0 := by
    calc
      R = (c.re + R) - c.re := by
        exact (add_sub_cancel_left c.re R).symm
      _ = c.re - c.re := by
        exact congrArg (fun t : ℝ => t - c.re) hadd
      _ = 0 := by
        exact sub_self c.re
  exact (ne_of_gt hR) hzero

/-- The left side of a positive-radius centered square avoids its centre. -/
theorem finiteRectangleSquareLeftSide_ne_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) (y : ℝ) :
    ((c.re - R : ℝ) : ℂ) + y * Complex.I ≠ c := by
  intro h
  have hre_eq :
      (((c.re - R : ℝ) : ℂ) + y * Complex.I).re = c.re :=
    congrArg Complex.re h
  have hre_left :
      (((c.re - R : ℝ) : ℂ) + y * Complex.I).re = c.re - R :=
    ofReal_add_mul_I_re (c.re - R) y
  have hsub :
      c.re - R = c.re :=
    Eq.trans hre_left.symm hre_eq
  have hzero :
      R = 0 := by
    calc
      R = c.re - (c.re - R) := by
        exact (sub_sub_self c.re R).symm
      _ = c.re - c.re := by
        exact congrArg (fun t : ℝ => c.re - t) hsub
      _ = 0 := by
        exact sub_self c.re
  exact (ne_of_gt hR) hzero

/-- Sub-sink (additivity): the square boundary integral is additive in the integrand when both
summands are continuous on the punctured closed square (hence interval-integrable on each of the
four sides, which avoid the centre `c`).  Uses `intervalIntegral.integral_add` per side. -/
theorem finiteRectangleSquareBoundaryIntegral_add
    (c : ℂ) {R : ℝ} (hR : 0 < R) (u v : ℂ → ℂ)
    (hu : ContinuousOn u ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hv : ContinuousOn v ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c})) :
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => u z + v z) c R =
      finiteRectangleSquareBoundaryIntegral u c R +
        finiteRectangleSquareBoundaryIntegral v c R := by
  let S : Set ℂ := ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c})
  have hbottom_mem :
      ∀ x : ℝ, x ∈ Set.uIcc (c.re - R) (c.re + R) →
        x + (((c.im - R : ℝ) : ℂ) * Complex.I) ∈ S := by
    intro x hx
    have hre :
        (x + (((c.im - R : ℝ) : ℂ) * Complex.I) : ℂ).re = x :=
      ofReal_add_mul_I_re x (c.im - R)
    have him :
        (x + (((c.im - R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im - R :=
      ofReal_add_mul_I_im x (c.im - R)
    exact
      And.intro
        (And.intro
          (by
            exact Eq.subst
              (motive := fun r : ℝ => r ∈ Set.uIcc (c.re - R) (c.re + R))
              hre.symm
              hx)
          (by
            exact Eq.subst
              (motive := fun y : ℝ => y ∈ Set.uIcc (c.im - R) (c.im + R))
              him.symm
              Set.left_mem_uIcc))
        (finiteRectangleSquareBottomSide_ne_center c hR x)
  have htop_mem :
      ∀ x : ℝ, x ∈ Set.uIcc (c.re - R) (c.re + R) →
        x + (((c.im + R : ℝ) : ℂ) * Complex.I) ∈ S := by
    intro x hx
    have hre :
        (x + (((c.im + R : ℝ) : ℂ) * Complex.I) : ℂ).re = x :=
      ofReal_add_mul_I_re x (c.im + R)
    have him :
        (x + (((c.im + R : ℝ) : ℂ) * Complex.I) : ℂ).im = c.im + R :=
      ofReal_add_mul_I_im x (c.im + R)
    exact
      And.intro
        (And.intro
          (by
            exact Eq.subst
              (motive := fun r : ℝ => r ∈ Set.uIcc (c.re - R) (c.re + R))
              hre.symm
              hx)
          (by
            exact Eq.subst
              (motive := fun y : ℝ => y ∈ Set.uIcc (c.im - R) (c.im + R))
              him.symm
              Set.right_mem_uIcc))
        (finiteRectangleSquareTopSide_ne_center c hR x)
  have hright_mem :
      ∀ y : ℝ, y ∈ Set.uIcc (c.im - R) (c.im + R) →
        ((c.re + R : ℝ) : ℂ) + y * Complex.I ∈ S := by
    intro y hy
    have hre :
        (((c.re + R : ℝ) : ℂ) + y * Complex.I).re = c.re + R :=
      ofReal_add_mul_I_re (c.re + R) y
    have him :
        (((c.re + R : ℝ) : ℂ) + y * Complex.I).im = y :=
      ofReal_add_mul_I_im (c.re + R) y
    exact
      And.intro
        (And.intro
          (by
            exact Eq.subst
              (motive := fun r : ℝ => r ∈ Set.uIcc (c.re - R) (c.re + R))
              hre.symm
              Set.right_mem_uIcc)
          (by
            exact Eq.subst
              (motive := fun t : ℝ => t ∈ Set.uIcc (c.im - R) (c.im + R))
              him.symm
              hy))
        (finiteRectangleSquareRightSide_ne_center c hR y)
  have hleft_mem :
      ∀ y : ℝ, y ∈ Set.uIcc (c.im - R) (c.im + R) →
        ((c.re - R : ℝ) : ℂ) + y * Complex.I ∈ S := by
    intro y hy
    have hre :
        (((c.re - R : ℝ) : ℂ) + y * Complex.I).re = c.re - R :=
      ofReal_add_mul_I_re (c.re - R) y
    have him :
        (((c.re - R : ℝ) : ℂ) + y * Complex.I).im = y :=
      ofReal_add_mul_I_im (c.re - R) y
    exact
      And.intro
        (And.intro
          (by
            exact Eq.subst
              (motive := fun r : ℝ => r ∈ Set.uIcc (c.re - R) (c.re + R))
              hre.symm
              Set.left_mem_uIcc)
          (by
            exact Eq.subst
              (motive := fun t : ℝ => t ∈ Set.uIcc (c.im - R) (c.im + R))
              him.symm
              hy))
        (finiteRectangleSquareLeftSide_ne_center c hR y)
  have hbottom_cont :
      ContinuousOn (fun x : ℝ => x + (((c.im - R : ℝ) : ℂ) * Complex.I))
        (Set.uIcc (c.re - R) (c.re + R)) :=
    (continuous_ofReal.add continuous_const).continuousOn
  have htop_cont :
      ContinuousOn (fun x : ℝ => x + (((c.im + R : ℝ) : ℂ) * Complex.I))
        (Set.uIcc (c.re - R) (c.re + R)) :=
    (continuous_ofReal.add continuous_const).continuousOn
  have hright_cont :
      ContinuousOn (fun y : ℝ => ((c.re + R : ℝ) : ℂ) + y * Complex.I)
        (Set.uIcc (c.im - R) (c.im + R)) :=
    (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
  have hleft_cont :
      ContinuousOn (fun y : ℝ => ((c.re - R : ℝ) : ℂ) + y * Complex.I)
        (Set.uIcc (c.im - R) (c.im + R)) :=
    (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
  have hu_bottom :
      IntervalIntegrable
        (fun x : ℝ => u (x + (((c.im - R : ℝ) : ℂ) * Complex.I)))
        volume (c.re - R) (c.re + R) :=
    (ContinuousOn.comp hu hbottom_cont hbottom_mem).intervalIntegrable
  have hv_bottom :
      IntervalIntegrable
        (fun x : ℝ => v (x + (((c.im - R : ℝ) : ℂ) * Complex.I)))
        volume (c.re - R) (c.re + R) :=
    (ContinuousOn.comp hv hbottom_cont hbottom_mem).intervalIntegrable
  have hu_top :
      IntervalIntegrable
        (fun x : ℝ => u (x + (((c.im + R : ℝ) : ℂ) * Complex.I)))
        volume (c.re - R) (c.re + R) :=
    (ContinuousOn.comp hu htop_cont htop_mem).intervalIntegrable
  have hv_top :
      IntervalIntegrable
        (fun x : ℝ => v (x + (((c.im + R : ℝ) : ℂ) * Complex.I)))
        volume (c.re - R) (c.re + R) :=
    (ContinuousOn.comp hv htop_cont htop_mem).intervalIntegrable
  have hu_right :
      IntervalIntegrable
        (fun y : ℝ => u (((c.re + R : ℝ) : ℂ) + y * Complex.I))
        volume (c.im - R) (c.im + R) :=
    (ContinuousOn.comp hu hright_cont hright_mem).intervalIntegrable
  have hv_right :
      IntervalIntegrable
        (fun y : ℝ => v (((c.re + R : ℝ) : ℂ) + y * Complex.I))
        volume (c.im - R) (c.im + R) :=
    (ContinuousOn.comp hv hright_cont hright_mem).intervalIntegrable
  have hu_left :
      IntervalIntegrable
        (fun y : ℝ => u (((c.re - R : ℝ) : ℂ) + y * Complex.I))
        volume (c.im - R) (c.im + R) :=
    (ContinuousOn.comp hu hleft_cont hleft_mem).intervalIntegrable
  have hv_left :
      IntervalIntegrable
        (fun y : ℝ => v (((c.re - R : ℝ) : ℂ) + y * Complex.I))
        volume (c.im - R) (c.im + R) :=
    (ContinuousOn.comp hv hleft_cont hleft_mem).intervalIntegrable
  let ub : ℂ := ∫ x : ℝ in (c.re - R)..(c.re + R),
    u (x + (((c.im - R : ℝ) : ℂ) * Complex.I))
  let vb : ℂ := ∫ x : ℝ in (c.re - R)..(c.re + R),
    v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))
  let ut : ℂ := ∫ x : ℝ in (c.re - R)..(c.re + R),
    u (x + (((c.im + R : ℝ) : ℂ) * Complex.I))
  let vt : ℂ := ∫ x : ℝ in (c.re - R)..(c.re + R),
    v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))
  let ur : ℂ := ∫ y : ℝ in (c.im - R)..(c.im + R),
    u (((c.re + R : ℝ) : ℂ) + y * Complex.I)
  let vr : ℂ := ∫ y : ℝ in (c.im - R)..(c.im + R),
    v (((c.re + R : ℝ) : ℂ) + y * Complex.I)
  let ul : ℂ := ∫ y : ℝ in (c.im - R)..(c.im + R),
    u (((c.re - R : ℝ) : ℂ) + y * Complex.I)
  let vl : ℂ := ∫ y : ℝ in (c.im - R)..(c.im + R),
    v (((c.re - R : ℝ) : ℂ) + y * Complex.I)
  have hbottom :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          u (x + (((c.im - R : ℝ) : ℂ) * Complex.I)) +
            v (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) =
        ub + vb :=
    intervalIntegral.integral_add hu_bottom hv_bottom
  have htop :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          u (x + (((c.im + R : ℝ) : ℂ) * Complex.I)) +
            v (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) =
        ut + vt :=
    intervalIntegral.integral_add hu_top hv_top
  have hright :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          u (((c.re + R : ℝ) : ℂ) + y * Complex.I) +
            v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) =
        ur + vr :=
    intervalIntegral.integral_add hu_right hv_right
  have hleft :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          u (((c.re - R : ℝ) : ℂ) + y * Complex.I) +
            v (((c.re - R : ℝ) : ℂ) + y * Complex.I)) =
        ul + vl :=
    intervalIntegral.integral_add hu_left hv_left
  have halgebra :
      (ub + vb) - (ut + vt) + Complex.I • (ur + vr) - Complex.I • (ul + vl) =
        (ub - ut + Complex.I • ur - Complex.I • ul) +
          (vb - vt + Complex.I • vr - Complex.I • vl) := by
    calc
      (ub + vb) - (ut + vt) + Complex.I • (ur + vr) - Complex.I • (ul + vl) =
          ((ub + vb) + (-(ut + vt))) +
              (Complex.I • ur + Complex.I • vr) -
            (Complex.I • ul + Complex.I • vl) := by
        exact
          congrArg₂
            (fun x y : ℂ => (ub + vb) - (ut + vt) + x - y)
            (smul_add Complex.I ur vr)
            (smul_add Complex.I ul vl)
      _ =
          ((ub + vb) + (-ut + -vt)) +
              (Complex.I • ur + Complex.I • vr) -
            (Complex.I • ul + Complex.I • vl) := by
        exact
          congrArg
            (fun x : ℂ =>
              ((ub + vb) + x) + (Complex.I • ur + Complex.I • vr) -
                (Complex.I • ul + Complex.I • vl))
            (neg_add ut vt)
      _ =
          (ub + (-ut) + Complex.I • ur + -(Complex.I • ul)) +
            (vb + (-vt) + Complex.I • vr + -(Complex.I • vl)) := by
        let p : ℂ := ub + (-ut)
        let q : ℂ := vb + (-vt)
        let r : ℂ := Complex.I • ur
        let s : ℂ := Complex.I • vr
        let t : ℂ := -(Complex.I • ul)
        let w : ℂ := -(Complex.I • vl)
        have hfirst :
            ((ub + vb) + (-ut + -vt)) = p + q := by
          calc
            ((ub + vb) + (-ut + -vt)) =
                (ub + (-ut)) + (vb + -vt) := by
              exact add_add_add_comm ub vb (-ut) (-vt)
            _ = p + q := by
              exact Eq.refl _
        have hlast :
            -(Complex.I • ul + Complex.I • vl) = t + w := by
          calc
            -(Complex.I • ul + Complex.I • vl) =
                -(Complex.I • ul) + -(Complex.I • vl) := by
              exact neg_add (Complex.I • ul) (Complex.I • vl)
            _ = t + w := by
              exact Eq.refl _
        have hsplit :
            (p + q) + (r + s) + (t + w) = (p + r + t) + (q + s + w) := by
          calc
            (p + q) + (r + s) + (t + w) =
                ((p + r) + (q + s)) + (t + w) := by
              exact congrArg (fun x : ℂ => x + (t + w)) (add_add_add_comm p q r s)
            _ = ((p + r) + t) + ((q + s) + w) := by
              exact add_add_add_comm (p + r) (q + s) t w
            _ = (p + r + t) + (q + s + w) := by
              exact Eq.refl _
        calc
          ((ub + vb) + (-ut + -vt)) +
                (Complex.I • ur + Complex.I • vr) -
              (Complex.I • ul + Complex.I • vl) =
              (p + q) + (r + s) + (t + w) := by
            exact
              congrArg₂
                (fun x y : ℂ => x + (r + s) + y)
                hfirst
                hlast
          _ = (p + r + t) + (q + s + w) := by
            exact hsplit
          _ =
              (ub + (-ut) + Complex.I • ur + -(Complex.I • ul)) +
                (vb + (-vt) + Complex.I • vr + -(Complex.I • vl)) := by
            exact Eq.refl _
      _ =
          (ub - ut + Complex.I • ur - Complex.I • ul) +
            (vb - vt + Complex.I • vr - Complex.I • vl) := by
        exact Eq.refl _
  calc
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => u z + v z) c R =
        (ub + vb) - (ut + vt) + Complex.I • (ur + vr) - Complex.I • (ul + vl) := by
      exact
        Eq.trans
          (finiteRectangleSquareBoundaryIntegral_eq (fun z : ℂ => u z + v z) c R)
          ((congrArg₂
            (fun bottom top : ℂ =>
              bottom - top +
                Complex.I •
                  (∫ y : ℝ in (c.im - R)..(c.im + R),
                    u (((c.re + R : ℝ) : ℂ) + y * Complex.I) +
                      v (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in (c.im - R)..(c.im + R),
                    u (((c.re - R : ℝ) : ℂ) + y * Complex.I) +
                      v (((c.re - R : ℝ) : ℂ) + y * Complex.I)))
            hbottom htop).trans
            (congrArg₂
              (fun right left : ℂ =>
                (ub + vb) - (ut + vt) + Complex.I • right - Complex.I • left)
              hright hleft))
    _ =
        (ub - ut + Complex.I • ur - Complex.I • ul) +
          (vb - vt + Complex.I • vr - Complex.I • vl) := by
      exact halgebra
    _ =
        finiteRectangleSquareBoundaryIntegral u c R +
          finiteRectangleSquareBoundaryIntegral v c R := by
      exact congrArg₂ (fun x y : ℂ => x + y)
        (finiteRectangleSquareBoundaryIntegral_eq u c R).symm
        (finiteRectangleSquareBoundaryIntegral_eq v c R).symm

/-- Sub-sink (remainder continuity): the residue-corrected remainder is continuous on the
punctured closed square.  There `(z - c) ≠ 0`, so `g = ((· - c) * g) * (· - c)⁻¹` is continuous
from `hcontinuous`, and `residue • (· - c)⁻¹` is continuous. -/
theorem finiteRectangleSquareBoundaryIntegral_residueRemainder_continuousOn
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c})) :
    ContinuousOn (fun z : ℂ => g z - residue • (z - c)⁻¹)
      ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}) := by
  let S : Set ℂ := ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c})
  have hsub :
      ContinuousOn (fun z : ℂ => z - c) S :=
    continuousOn_id.sub continuousOn_const
  have hnonzero :
      ∀ z : ℂ, z ∈ S → z - c ≠ 0 := by
    intro z hz hzero
    have hz_ne : z ≠ c := hz.2
    have hz_eq : z = c := sub_eq_zero.mp hzero
    exact hz_ne hz_eq
  have hinv :
      ContinuousOn (fun z : ℂ => (z - c)⁻¹) S :=
    hsub.inv₀ hnonzero
  have hpole :
      ContinuousOn (fun z : ℂ => residue • (z - c)⁻¹) S :=
    hinv.const_smul residue
  have hquot :
      ContinuousOn (fun z : ℂ => ((z - c) * g z) * (z - c)⁻¹) S :=
    hcontinuous.mul hinv
  have hraw :
      ContinuousOn
        (fun z : ℂ => ((z - c) * g z) * (z - c)⁻¹ -
          residue • (z - c)⁻¹) S :=
    hquot.sub hpole
  exact hraw.congr
    (fun z hz =>
      congrArg (fun x : ℂ => x - residue • (z - c)⁻¹)
        (calc
          g z = 1 * g z := by
            exact (one_mul (g z)).symm
          _ = ((z - c) * (z - c)⁻¹) * g z := by
            exact congrArg (fun x : ℂ => x * g z)
              (mul_inv_cancel₀ (hnonzero z hz)).symm
          _ = ((z - c) * g z) * (z - c)⁻¹ := by
            calc
              ((z - c) * (z - c)⁻¹) * g z =
                  (z - c) * ((z - c)⁻¹ * g z) := by
                exact mul_assoc (z - c) (z - c)⁻¹ (g z)
              _ = (z - c) * (g z * (z - c)⁻¹) := by
                exact congrArg (fun x : ℂ => (z - c) * x)
                  (mul_comm (z - c)⁻¹ (g z))
              _ = ((z - c) * g z) * (z - c)⁻¹ := by
                exact (mul_assoc (z - c) (g z) (z - c)⁻¹).symm))

/-- Sub-sink (pole-kernel continuity): `residue • (· - c)⁻¹` is continuous on the punctured
closed square (the centre `c` is removed). -/
theorem finiteRectangleSquareBoundaryIntegral_poleKernel_smul_continuousOn
    (c : ℂ) {R : ℝ} (hR : 0 < R) (residue : ℂ) :
    ContinuousOn (fun z : ℂ => residue • (z - c)⁻¹)
      ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}) := by
  have hsub :
      ContinuousOn (fun z : ℂ => z - c)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}) :=
    continuousOn_id.sub continuousOn_const
  have hnonzero :
      ∀ z : ℂ,
        z ∈ ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}) →
          z - c ≠ 0 := by
    intro z hz hzero
    have hz_ne : z ≠ c := hz.2
    have hz_eq : z = c := sub_eq_zero.mp hzero
    exact hz_ne hz_eq
  exact (hsub.inv₀ hnonzero).const_smul residue

/-- Sink (linearity leaf): the square boundary integral splits over the residue
decomposition `g = (g - residue • (· - c)⁻¹) + residue • (· - c)⁻¹`.

Thin wrapper: rewrite `g` as the pointwise sum (`sub_add_cancel`), split by additivity
(`...add`, with the two continuity sub-sinks), and pull the scalar out by homogeneity
(`...smul`). -/
theorem finiteRectangleSquareBoundaryIntegral_residue_split
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c})) :
    finiteRectangleSquareBoundaryIntegral g c R =
      finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => g z - residue • (z - c)⁻¹) c R +
        residue • finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R :=
  calc
    finiteRectangleSquareBoundaryIntegral g c R =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => (g z - residue • (z - c)⁻¹) + residue • (z - c)⁻¹) c R :=
      congrArg (fun φ : ℂ → ℂ => finiteRectangleSquareBoundaryIntegral φ c R)
        (funext (fun z => (sub_add_cancel (g z) (residue • (z - c)⁻¹)).symm))
    _ =
        finiteRectangleSquareBoundaryIntegral (fun z : ℂ => g z - residue • (z - c)⁻¹) c R +
          finiteRectangleSquareBoundaryIntegral (fun z : ℂ => residue • (z - c)⁻¹) c R :=
      finiteRectangleSquareBoundaryIntegral_add c hR
        (fun z : ℂ => g z - residue • (z - c)⁻¹)
        (fun z : ℂ => residue • (z - c)⁻¹)
        (finiteRectangleSquareBoundaryIntegral_residueRemainder_continuousOn c hR g residue
          hcontinuous)
        (finiteRectangleSquareBoundaryIntegral_poleKernel_smul_continuousOn c hR residue)
    _ =
        finiteRectangleSquareBoundaryIntegral (fun z : ℂ => g z - residue • (z - c)⁻¹) c R +
          residue • finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R :=
      congrArg
        (fun x : ℂ =>
          finiteRectangleSquareBoundaryIntegral (fun z : ℂ => g z - residue • (z - c)⁻¹) c R + x)
        (finiteRectangleSquareBoundaryIntegral_smul c R residue (fun z : ℂ => (z - c)⁻¹))

/-- Sub-sink (square Cauchy–Goursat): a function continuous on the closed square and
holomorphic on its open interior has square boundary integral zero.  This is
`finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiableOn` (`Part10`)
specialised to the square corners via the corner real/imaginary coordinate lemmas. -/
theorem finiteRectangleSquareBoundaryIntegral_eq_zero_of_holomorphicOn
    (c : ℂ) {R : ℝ} (hR : 0 < R) (G : ℂ → ℂ)
    (Hc : ContinuousOn G (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)))
    (Hd :
      DifferentiableOn ℂ G
        (Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R))) :
    finiteRectangleSquareBoundaryIntegral G c R = 0 := by
  let z : ℂ := finiteRectangleSquareLowerCorner c R
  let w : ℂ := finiteRectangleSquareUpperCorner c R
  have hz_re : z.re = c.re - R := by
    exact finiteRectangleSquareLowerCorner_re c R
  have hw_re : w.re = c.re + R := by
    exact finiteRectangleSquareUpperCorner_re c R
  have hz_im : z.im = c.im - R := by
    exact finiteRectangleSquareLowerCorner_im c R
  have hw_im : w.im = c.im + R := by
    exact finiteRectangleSquareUpperCorner_im c R
  have hre_lt : z.re < w.re := by
    exact finiteRectangleSquareLowerCorner_re_lt_upperCorner_re c hR
  have him_lt : z.im < w.im := by
    exact finiteRectangleSquareLowerCorner_im_lt_upperCorner_im c hR
  have hclosed :
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) =
        (Set.uIcc (c.re - R) (c.re + R) ×ℂ
          Set.uIcc (c.im - R) (c.im + R)) :=
    congrArg₂ Set.reProdIm
      (congrArg₂ Set.uIcc hz_re hw_re)
      (congrArg₂ Set.uIcc hz_im hw_im)
  have hmin_re : min z.re w.re = c.re - R := by
    exact Eq.trans (inf_eq_left.mpr (le_of_lt hre_lt)) hz_re
  have hmax_re : max z.re w.re = c.re + R := by
    exact Eq.trans (sup_eq_right.mpr (le_of_lt hre_lt)) hw_re
  have hmin_im : min z.im w.im = c.im - R := by
    exact Eq.trans (inf_eq_left.mpr (le_of_lt him_lt)) hz_im
  have hmax_im : max z.im w.im = c.im + R := by
    exact Eq.trans (sup_eq_right.mpr (le_of_lt him_lt)) hw_im
  have hopen :
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im)) =
        (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) :=
    congrArg₂ Set.reProdIm
      (congrArg₂ Set.Ioo hmin_re hmax_re)
      (congrArg₂ Set.Ioo hmin_im hmax_im)
  have Hc_cell : ContinuousOn G (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
    Eq.subst
      (motive := fun S : Set ℂ => ContinuousOn G S)
      hclosed.symm
      Hc
  have Hd_cell :
      DifferentiableOn ℂ G
        (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
          Set.Ioo (min z.im w.im) (max z.im w.im)) :=
    Eq.subst
      (motive := fun S : Set ℂ => DifferentiableOn ℂ G S)
      hopen.symm
      Hd
  exact
    Eq.trans
      (finiteRectangleSquareBoundaryIntegral_eq_cellBoundary G c R)
      (finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiableOn
        G z w Hc_cell Hd_cell)

/-- Sub-sink (square Cauchy-Goursat off countable): a function continuous on the
closed square and holomorphic on its open interior away from a countable exceptional
set has square boundary integral zero. -/
theorem finiteRectangleSquareBoundaryIntegral_eq_zero_of_holomorphicOn_off_countable
    (c : ℂ) {R : ℝ} (hR : 0 < R) (G : ℂ → ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn G (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)))
    (Hd :
      ∀ z : ℂ,
        z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) \ s →
          DifferentiableAt ℂ G z) :
    finiteRectangleSquareBoundaryIntegral G c R = 0 := by
  let z : ℂ := finiteRectangleSquareLowerCorner c R
  let w : ℂ := finiteRectangleSquareUpperCorner c R
  have hz_re : z.re = c.re - R := by
    exact finiteRectangleSquareLowerCorner_re c R
  have hw_re : w.re = c.re + R := by
    exact finiteRectangleSquareUpperCorner_re c R
  have hz_im : z.im = c.im - R := by
    exact finiteRectangleSquareLowerCorner_im c R
  have hw_im : w.im = c.im + R := by
    exact finiteRectangleSquareUpperCorner_im c R
  have hre_lt : z.re < w.re := by
    exact finiteRectangleSquareLowerCorner_re_lt_upperCorner_re c hR
  have him_lt : z.im < w.im := by
    exact finiteRectangleSquareLowerCorner_im_lt_upperCorner_im c hR
  have hclosed :
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) =
        (Set.uIcc (c.re - R) (c.re + R) ×ℂ
          Set.uIcc (c.im - R) (c.im + R)) :=
    congrArg₂ Set.reProdIm
      (congrArg₂ Set.uIcc hz_re hw_re)
      (congrArg₂ Set.uIcc hz_im hw_im)
  have hmin_re : min z.re w.re = c.re - R := by
    exact Eq.trans (inf_eq_left.mpr (le_of_lt hre_lt)) hz_re
  have hmax_re : max z.re w.re = c.re + R := by
    exact Eq.trans (sup_eq_right.mpr (le_of_lt hre_lt)) hw_re
  have hmin_im : min z.im w.im = c.im - R := by
    exact Eq.trans (inf_eq_left.mpr (le_of_lt him_lt)) hz_im
  have hmax_im : max z.im w.im = c.im + R := by
    exact Eq.trans (sup_eq_right.mpr (le_of_lt him_lt)) hw_im
  have hopen :
      (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im)) =
        (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) :=
    congrArg₂ Set.reProdIm
      (congrArg₂ Set.Ioo hmin_re hmax_re)
      (congrArg₂ Set.Ioo hmin_im hmax_im)
  have Hc_cell : ContinuousOn G (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
    Eq.subst
      (motive := fun S : Set ℂ => ContinuousOn G S)
      hclosed.symm
      Hc
  have Hd_cell :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im) \ s →
          DifferentiableAt ℂ G x :=
    Eq.subst
      (motive := fun S : Set ℂ =>
        ∀ x : ℂ, x ∈ S \ s → DifferentiableAt ℂ G x)
      hopen.symm
      Hd
  exact
    Eq.trans
      (finiteRectangleSquareBoundaryIntegral_eq_cellBoundary G c R)
      (finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
        G z w s hs Hc_cell Hd_cell)

/-- Sub-sink (boundary invariance off the centre): the square boundary integral depends only on
the values away from the centre `c`, since the four oriented sides (at distance `R > 0` from
`c`) never pass through `c`. -/
theorem finiteRectangleSquareBoundaryIntegral_eq_of_eqOffCenter
    (c : ℂ) {R : ℝ} (hR : 0 < R) (G H : ℂ → ℂ)
    (hGH : ∀ z : ℂ, z ≠ c → G z = H z) :
    finiteRectangleSquareBoundaryIntegral G c R =
      finiteRectangleSquareBoundaryIntegral H c R := by
  have hbottom :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          G (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) =
        ∫ x : ℝ in (c.re - R)..(c.re + R),
          H (x + (((c.im - R : ℝ) : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr
      (fun x _ =>
        hGH (x + (((c.im - R : ℝ) : ℂ) * Complex.I))
          (finiteRectangleSquareBottomSide_ne_center c hR x))
  have htop :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          G (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) =
        ∫ x : ℝ in (c.re - R)..(c.re + R),
          H (x + (((c.im + R : ℝ) : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr
      (fun x _ =>
        hGH (x + (((c.im + R : ℝ) : ℂ) * Complex.I))
          (finiteRectangleSquareTopSide_ne_center c hR x))
  have hright :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          G (((c.re + R : ℝ) : ℂ) + y * Complex.I)) =
        ∫ y : ℝ in (c.im - R)..(c.im + R),
          H (((c.re + R : ℝ) : ℂ) + y * Complex.I) :=
    intervalIntegral.integral_congr
      (fun y _ =>
        hGH (((c.re + R : ℝ) : ℂ) + y * Complex.I)
          (finiteRectangleSquareRightSide_ne_center c hR y))
  have hleft :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          G (((c.re - R : ℝ) : ℂ) + y * Complex.I)) =
        ∫ y : ℝ in (c.im - R)..(c.im + R),
          H (((c.re - R : ℝ) : ℂ) + y * Complex.I) :=
    intervalIntegral.integral_congr
      (fun y _ =>
        hGH (((c.re - R : ℝ) : ℂ) + y * Complex.I)
          (finiteRectangleSquareLeftSide_ne_center c hR y))
  calc
    finiteRectangleSquareBoundaryIntegral G c R =
        (∫ x : ℝ in (c.re - R)..(c.re + R),
            G (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in (c.re - R)..(c.re + R),
            G (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in (c.im - R)..(c.im + R),
                G (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  G (((c.re - R : ℝ) : ℂ) + y * Complex.I)) := by
      exact finiteRectangleSquareBoundaryIntegral_eq G c R
    _ =
        (∫ x : ℝ in (c.re - R)..(c.re + R),
            H (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in (c.re - R)..(c.re + R),
            H (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in (c.im - R)..(c.im + R),
                H (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  H (((c.re - R : ℝ) : ℂ) + y * Complex.I)) := by
      exact
        (congrArg₂
          (fun bottom top : ℂ =>
            bottom - top +
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  G (((c.re + R : ℝ) : ℂ) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (c.im - R)..(c.im + R),
                  G (((c.re - R : ℝ) : ℂ) + y * Complex.I)))
          hbottom htop).trans
          (congrArg₂
            (fun right left : ℂ =>
                (∫ x : ℝ in (c.re - R)..(c.re + R),
                  H (x + (((c.im - R : ℝ) : ℂ) * Complex.I))) -
                (∫ x : ℝ in (c.re - R)..(c.re + R),
                  H (x + (((c.im + R : ℝ) : ℂ) * Complex.I))) +
                  Complex.I • right - Complex.I • left)
            hright hleft)
    _ = finiteRectangleSquareBoundaryIntegral H c R := by
      exact (finiteRectangleSquareBoundaryIntegral_eq H c R).symm

/-- The residue-corrected remainder is the punctured difference quotient of
`F z = (z - c) * g z` after filling `F c` with the residue. -/
theorem finiteRectangleSquareBoundaryIntegral_residueRemainder_eq_dslope_off_center
    (c : ℂ) (g : ℂ → ℂ) (residue : ℂ) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, z ≠ c → F z = (z - c) * g z)
    (hFc : F c = residue) :
    ∀ z : ℂ, z ≠ c →
      dslope F c z = g z - residue • (z - c)⁻¹ := by
  intro z hz
  have hFz : F z = (z - c) * g z :=
    hF z hz
  calc
    dslope F c z = (z - c)⁻¹ • (F z - F c) := by
      exact dslope_of_ne F hz
    _ = (z - c)⁻¹ * (((z - c) * g z) - residue) := by
      exact congrArg (fun w : ℂ => (z - c)⁻¹ * w)
        (congrArg₂ (fun x y : ℂ => x - y) hFz hFc)
    _ = (z - c)⁻¹ * ((z - c) * g z) - (z - c)⁻¹ * residue := by
      exact mul_sub (z - c)⁻¹ ((z - c) * g z) residue
    _ = ((z - c)⁻¹ * (z - c)) * g z - (z - c)⁻¹ * residue := by
      exact congrArg (fun w : ℂ => w - (z - c)⁻¹ * residue)
        (mul_assoc (z - c)⁻¹ (z - c) (g z)).symm
    _ = 1 * g z - (z - c)⁻¹ * residue := by
      exact congrArg
        (fun w : ℂ => w * g z - (z - c)⁻¹ * residue)
        (inv_mul_cancel₀ (sub_ne_zero.mpr hz))
    _ = g z - (z - c)⁻¹ * residue := by
      exact congrArg (fun w : ℂ => w - (z - c)⁻¹ * residue) (one_mul (g z))
    _ = g z - residue * (z - c)⁻¹ := by
      exact congrArg (fun w : ℂ => g z - w) (mul_comm (z - c)⁻¹ residue)
    _ = g z - residue • (z - c)⁻¹ := by
      exact Eq.refl _

/-- A positive-radius closed square is a neighborhood of its center. -/
theorem finiteRectangleSquareBoundaryIntegral_closedSquare_mem_nhds_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) ∈ 𝓝 c := by
  have hre_order : c.re - R ≤ c.re + R :=
    le_of_lt
      (calc
        c.re - R < c.re := by
          exact sub_lt_self c.re hR
        _ < c.re + R := by
          exact lt_add_of_pos_right c.re hR)
  have him_order : c.im - R ≤ c.im + R :=
    le_of_lt
      (calc
        c.im - R < c.im := by
          exact sub_lt_self c.im hR
        _ < c.im + R := by
          exact lt_add_of_pos_right c.im hR)
  have hre_mem : c.re ∈ Set.Ioo (c.re - R) (c.re + R) :=
    And.intro (sub_lt_self c.re hR) (lt_add_of_pos_right c.re hR)
  have him_mem : c.im ∈ Set.Ioo (c.im - R) (c.im + R) :=
    And.intro (sub_lt_self c.im hR) (lt_add_of_pos_right c.im hR)
  have hordered :
      (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) =
        (Set.Icc (c.re - R) (c.re + R) ×ℂ
          Set.Icc (c.im - R) (c.im + R)) := by
    exact congrArg₂ Set.reProdIm
      (Set.uIcc_of_le hre_order)
      (Set.uIcc_of_le him_order)
  have hmem_interior_ordered :
      c ∈ interior
        (Set.Icc (c.re - R) (c.re + R) ×ℂ
          Set.Icc (c.im - R) (c.im + R)) := by
    exact
      Eq.subst
        (motive := fun s : Set ℂ => c ∈ s)
        (interior_reProdIm
          (Set.Icc (c.re - R) (c.re + R))
          (Set.Icc (c.im - R) (c.im + R))).symm
        (Complex.mem_reProdIm.mpr
          (And.intro
            (Eq.subst
              (motive := fun s : Set ℝ => c.re ∈ s)
              (interior_Icc (a := c.re - R) (b := c.re + R)).symm
              hre_mem)
            (Eq.subst
              (motive := fun s : Set ℝ => c.im ∈ s)
              (interior_Icc (a := c.im - R) (b := c.im + R)).symm
              him_mem)))
  have hmem_interior :
      c ∈ interior (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) :=
    Eq.subst
      (motive := fun s : Set ℂ => c ∈ interior s)
      hordered.symm
      hmem_interior_ordered
  exact mem_interior_iff_mem_nhds.mp hmem_interior

/-- The divided slope of a continuous square extension is continuous on the
closed square once the extension is differentiable at the center. -/
theorem finiteRectangleSquareBoundaryIntegral_dslope_continuousOn_of_continuousOn_differentiableAt
    (c : ℂ) {R : ℝ} (hR : 0 < R) (F : ℂ → ℂ)
    (hFcont : ContinuousOn F (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)))
    (hFdiff : DifferentiableAt ℂ F c) :
    ContinuousOn (dslope F c) (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) := by
  exact
    (continuousOn_dslope
      (f := F)
      (a := c)
      (s := (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)))
      (finiteRectangleSquareBoundaryIntegral_closedSquare_mem_nhds_center c hR)).mpr
      ⟨hFcont, hFdiff⟩

/-- The open square around the center is a neighborhood of the center. -/
theorem finiteRectangleSquareBoundaryIntegral_openSquare_mem_nhds_center
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (Set.Ioo (c.re - R) (c.re + R) ×ℂ
      Set.Ioo (c.im - R) (c.im + R)) ∈ 𝓝 c := by
  exact
    (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds
      (Complex.mem_reProdIm.mpr
        (And.intro
          (And.intro (sub_lt_self c.re hR) (lt_add_of_pos_right c.re hR))
          (And.intro (sub_lt_self c.im hR) (lt_add_of_pos_right c.im hR))))

/-- The open coordinate square is contained in the corresponding closed square. -/
theorem finiteRectangleSquareBoundaryIntegral_openSquare_subset_closedSquare
    (c : ℂ) {R : ℝ} :
    (Set.Ioo (c.re - R) (c.re + R) ×ℂ
      Set.Ioo (c.im - R) (c.im + R)) ⊆
        (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) := by
  intro z hz
  exact
    Complex.mem_reProdIm.mpr
      (And.intro
        (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.1))
        (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.2)))

/-- Updating the centre value by the punctured limit gives continuity on the closed square. -/
theorem finiteRectangleSquareBoundaryIntegral_update_continuousOn_closedSquare
    (c : ℂ) {R : ℝ} (F : ℂ → ℂ) (residue : ℂ)
    (hcontinuous :
      ContinuousOn F
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hlocal : Tendsto F (𝓝[≠] c) (𝓝 residue)) :
    ContinuousOn (Function.update F c residue)
      (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) := by
  have hwithin :
      Tendsto F
        (𝓝[(Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}] c)
        (𝓝 residue) := by
    exact
      hlocal.mono_left
        (nhdsWithin_mono c
          (fun z hz hzc => hz.2 hzc))
  exact
    (continuousOn_update_iff
      (f := F)
      (s := (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)))
      (x := c)
      (y := residue)).mpr
      (And.intro hcontinuous (fun _ => hwithin))

/-- Away from the updated centre, the updated function has the same derivative behavior. -/
theorem finiteRectangleSquareBoundaryIntegral_update_differentiableAt_of_ne
    (c z : ℂ) (F : ℂ → ℂ) (residue : ℂ) (hz : z ≠ c)
    (hF : DifferentiableAt ℂ F z) :
    DifferentiableAt ℂ (Function.update F c residue) z := by
  have heq_on :
      Set.EqOn (Function.update F c residue) F {w : ℂ | w ≠ c} := by
    intro w hw
    exact Function.update_noteq hw residue F
  exact
    hF.congr_of_eventuallyEq
      (heq_on.eventuallyEq_of_mem (isOpen_ne.mem_nhds hz))

/-- A local closed ball inside an open square around any of its points. -/
theorem finiteRectangleSquareBoundaryIntegral_exists_closedBall_subset_openSquare
    (c z : ℂ) {R : ℝ}
    (hz :
      z ∈ Set.Ioo (c.re - R) (c.re + R) ×ℂ
        Set.Ioo (c.im - R) (c.im + R)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall z ρ ⊆
        (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) := by
  exact
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz)

/-- On a closed ball contained in the open square, the center-updated function is
complex differentiable off the inserted centre and the original exceptional set. -/
theorem finiteRectangleSquareBoundaryIntegral_update_differentiable_off_insert_on_ball
    (c z : ℂ) {R ρ : ℝ} (F : ℂ → ℂ) (residue : ℂ) (s : Set ℂ)
    (hball :
      Metric.closedBall z ρ ⊆
        (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)))
    (hdifferentiable :
      ∀ w : ℂ,
        w ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ F w) :
    ∀ w : ℂ,
      w ∈ Metric.ball z ρ \ insert c s →
        DifferentiableAt ℂ (Function.update F c residue) w := by
  intro w hw
  have hw_open :
      w ∈ Set.Ioo (c.re - R) (c.re + R) ×ℂ
        Set.Ioo (c.im - R) (c.im + R) :=
    hball (Metric.ball_subset_closedBall hw.1)
  have hw_ne : w ≠ c := by
    intro h_eq
    exact hw.2 (Eq.subst (motive := fun u : ℂ => u ∈ insert c s) h_eq.symm (Set.mem_insert c s))
  have hw_not_s : w ∉ s := by
    intro hws
    exact hw.2 (Set.mem_insert_of_mem c hws)
  exact
    finiteRectangleSquareBoundaryIntegral_update_differentiableAt_of_ne
      c w F residue hw_ne
      (hdifferentiable w
        (And.intro
          (And.intro hw_open hw_ne)
          hw_not_s))

/-- Owner lemma (off-countable removable extension for the product): the
product `F z = (z - c) * g z`, with its residue value inserted at `c`, is
continuous on the square, differentiable at `c`, and analytic on the interior
away from the original countable exceptional set. -/
theorem finiteRectangleSquareBoundaryIntegral_residueProduct_extension_off_countable_owner
    (c : ℂ) {R : ℝ} (hR : 0 < R) (F : ℂ → ℂ) (residue : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn F
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ F z)
    (hlocal : Tendsto F (𝓝[≠] c) (𝓝 residue)) :
    ∃ Fext : ℂ → ℂ,
      (∀ z : ℂ, z ≠ c → Fext z = F z) ∧
        Fext c = residue ∧
          ContinuousOn Fext (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) ∧
            DifferentiableAt ℂ Fext c ∧
              ∀ z : ℂ,
                z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
                  Set.Ioo (c.im - R) (c.im + R)) \ (insert c s) →
                  AnalyticAt ℂ Fext z := by
  let Fext : ℂ → ℂ := Function.update F c residue
  have hFext_off : ∀ z : ℂ, z ≠ c → Fext z = F z := by
    intro z hz
    exact Function.update_noteq hz residue F
  have hFext_c : Fext c = residue := by
    exact Function.update_same c residue F
  have hFext_cont :
      ContinuousOn Fext (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) :=
    finiteRectangleSquareBoundaryIntegral_update_continuousOn_closedSquare
      c F residue hcontinuous hlocal
  have hcenter_ball_exists :
      ∃ ρ : ℝ, 0 < ρ ∧
        Metric.closedBall c ρ ⊆
          (Set.Ioo (c.re - R) (c.re + R) ×ℂ
            Set.Ioo (c.im - R) (c.im + R)) :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      (finiteRectangleSquareBoundaryIntegral_openSquare_mem_nhds_center c hR)
  obtain ⟨ρc, hρc_pos, hρc_subset_open⟩ := hcenter_ball_exists
  let ρcnn : ℝ≥0 := ⟨ρc, le_of_lt hρc_pos⟩
  have hρcnn_pos : (0 : ℝ≥0) < ρcnn :=
    NNReal.coe_pos.mpr hρc_pos
  have hρc_subset_closed :
      Metric.closedBall c ρc ⊆
        (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) :=
    hρc_subset_open.trans
      (finiteRectangleSquareBoundaryIntegral_openSquare_subset_closedSquare c)
  have hFext_cont_center_ball :
      ContinuousOn Fext (Metric.closedBall c ρcnn) :=
    hFext_cont.mono hρc_subset_closed
  have hFext_diff_center_ball :
      ∀ w : ℂ,
        w ∈ Metric.ball c ρcnn \ insert c s →
          DifferentiableAt ℂ Fext w :=
    finiteRectangleSquareBoundaryIntegral_update_differentiable_off_insert_on_ball
      c c F residue s hρc_subset_open hdifferentiable
  have hFext_power_center :
      HasFPowerSeriesOnBall Fext (cauchyPowerSeries Fext c ρcnn) c ρcnn :=
    Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
      (Set.Countable.insert c hs)
      hFext_cont_center_ball
      hFext_diff_center_ball
      hρcnn_pos
  have hFext_diff_c : DifferentiableAt ℂ Fext c :=
    hFext_power_center.analyticAt.differentiableAt
  have hFext_analytic :
      ∀ z : ℂ,
        z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) \ (insert c s) →
          AnalyticAt ℂ Fext z := by
    intro z hz
    obtain ⟨ρz, hρz_pos, hρz_subset_open⟩ :=
      finiteRectangleSquareBoundaryIntegral_exists_closedBall_subset_openSquare
        c z hz.1
    let ρznn : ℝ≥0 := ⟨ρz, le_of_lt hρz_pos⟩
    have hρznn_pos : (0 : ℝ≥0) < ρznn :=
      NNReal.coe_pos.mpr hρz_pos
    have hρz_subset_closed :
        Metric.closedBall z ρz ⊆
          (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) :=
      hρz_subset_open.trans
        (finiteRectangleSquareBoundaryIntegral_openSquare_subset_closedSquare c)
    have hFext_cont_z_ball :
        ContinuousOn Fext (Metric.closedBall z ρznn) :=
      hFext_cont.mono hρz_subset_closed
    have hFext_diff_z_ball :
        ∀ w : ℂ,
          w ∈ Metric.ball z ρznn \ insert c s →
            DifferentiableAt ℂ Fext w :=
      finiteRectangleSquareBoundaryIntegral_update_differentiable_off_insert_on_ball
        c z F residue s hρz_subset_open hdifferentiable
    have hFext_power_z :
        HasFPowerSeriesOnBall Fext (cauchyPowerSeries Fext z ρznn) z ρznn :=
      Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
        (Set.Countable.insert c hs)
        hFext_cont_z_ball
        hFext_diff_z_ball
        hρznn_pos
    exact hFext_power_z.analyticAt
  exact
    Exists.intro Fext
      (And.intro hFext_off
        (And.intro hFext_c
          (And.intro hFext_cont
            (And.intro hFext_diff_c hFext_analytic))))

/-- Owner lemma (off-countable removable singularity): if a residue-corrected
remainder is differentiable away from a countable exceptional set and satisfies
the removable-growth condition at the puncture, then it has a continuous
extension to the square which is differentiable off the same exceptional set and
the puncture.

This is the countable-exception analogue of Mathlib
`Complex.differentiableOn_update_limUnder_insert_of_isLittleO`.  The standard
Mathlib theorem removes an isolated puncture after differentiability on a full
punctured neighborhood; this owner lemma is the exact stronger surface needed
for the finite-rectangle residue theorem, where Cauchy-Goursat is already
available off a countable exceptional set. -/
theorem finiteRectangleSquareBoundaryIntegral_residueRemainder_extension_off_countable_owner
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ (fun w : ℂ => (w - c) * g w) z)
    (hlocal : Tendsto (fun z : ℂ => (z - c) * g z) (𝓝[≠] c) (𝓝 residue)) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, z ≠ c → G z = g z - residue • (z - c)⁻¹) ∧
        ContinuousOn G (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) ∧
          ∀ z : ℂ,
            z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
              Set.Ioo (c.im - R) (c.im + R)) \ (insert c s) →
              DifferentiableAt ℂ G z := by
  let F : ℂ → ℂ := fun z : ℂ => (z - c) * g z
  obtain ⟨Fext, hFext_eq, hFext_c, hFext_cont, hFext_diff_c, hFext_an⟩ :=
    finiteRectangleSquareBoundaryIntegral_residueProduct_extension_off_countable_owner
      c hR F residue s hs hcontinuous hdifferentiable hlocal
  let G : ℂ → ℂ := dslope Fext c
  have hGeq :
      ∀ z : ℂ, z ≠ c → G z = g z - residue • (z - c)⁻¹ := by
    intro z hz
    exact
      finiteRectangleSquareBoundaryIntegral_residueRemainder_eq_dslope_off_center
        c g residue Fext
        (fun w hw => Eq.trans (hFext_eq w hw) (Eq.refl _))
        hFext_c z hz
  have hGcont :
      ContinuousOn G (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) := by
    exact
      finiteRectangleSquareBoundaryIntegral_dslope_continuousOn_of_continuousOn_differentiableAt
        c hR Fext hFext_cont hFext_diff_c
  have hGdiff :
      ∀ z : ℂ,
        z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
          Set.Ioo (c.im - R) (c.im + R)) \ (insert c s) →
          DifferentiableAt ℂ G z := by
    intro z hz
    have hz_ne : z ≠ c := by
      intro hzc
      have hz_mem_insert : z ∈ insert c s :=
        Eq.subst (motive := fun w : ℂ => w ∈ insert c s) hzc.symm
          (Set.mem_insert c s)
      exact hz.2 hz_mem_insert
    have hFan : AnalyticAt ℂ Fext z :=
      hFext_an z hz
    have hFdiff : DifferentiableAt ℂ Fext z :=
      hFan.differentiableAt
    exact (differentiableAt_dslope_of_ne hz_ne).mpr hFdiff
  exact ⟨G, hGeq, hGcont, hGdiff⟩

/-- Sub-sink (removable extension): the residue-corrected remainder
`g z - residue • (z - c)⁻¹` extends continuously to the square and is
holomorphic on the open square away from the original countable exceptional set
and the removable centre. -/
theorem finiteRectangleSquareBoundaryIntegral_residueRemainder_extension
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ (fun w : ℂ => (w - c) * g w) z)
    (hlocal : Tendsto (fun z : ℂ => (z - c) * g z) (𝓝[≠] c) (𝓝 residue)) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, z ≠ c → G z = g z - residue • (z - c)⁻¹) ∧
        ContinuousOn G (Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) ∧
          ∀ z : ℂ,
            z ∈ (Set.Ioo (c.re - R) (c.re + R) ×ℂ
              Set.Ioo (c.im - R) (c.im + R)) \ (insert c s) →
              DifferentiableAt ℂ G z := by
  exact
    finiteRectangleSquareBoundaryIntegral_residueRemainder_extension_off_countable_owner
      c hR g residue s hs hcontinuous hdifferentiable hlocal

/-- Sink (removable-singularity leaf): the residue-corrected remainder
`g z - residue • (z - c)⁻¹` has square boundary integral zero.

Thin wrapper: the remainder extends holomorphically across `c`
(`...residueRemainder_extension`); the boundary integral is unchanged by replacing the
remainder with that extension off the centre (`...eq_of_eqOffCenter`), and the extension's
boundary integral vanishes by square Cauchy–Goursat (`...eq_zero_of_holomorphicOn`). -/
theorem finiteRectangleSquareBoundaryIntegral_residueRemainder_eq_zero
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ (fun w : ℂ => (w - c) * g w) z)
    (hlocal : Tendsto (fun z : ℂ => (z - c) * g z) (𝓝[≠] c) (𝓝 residue)) :
    finiteRectangleSquareBoundaryIntegral
      (fun z : ℂ => g z - residue • (z - c)⁻¹) c R = 0 := by
  obtain ⟨G, hGeq, hGcont, hGdiff⟩ :=
    finiteRectangleSquareBoundaryIntegral_residueRemainder_extension
      c hR g residue s hs hcontinuous hdifferentiable hlocal
  have hexception_countable : (insert c s).Countable :=
    hs.insert c
  calc
    finiteRectangleSquareBoundaryIntegral (fun z : ℂ => g z - residue • (z - c)⁻¹) c R =
        finiteRectangleSquareBoundaryIntegral G c R :=
      (finiteRectangleSquareBoundaryIntegral_eq_of_eqOffCenter c hR
        (fun z : ℂ => g z - residue • (z - c)⁻¹) G
        (fun z hz => (hGeq z hz).symm))
    _ = 0 :=
      finiteRectangleSquareBoundaryIntegral_eq_zero_of_holomorphicOn_off_countable
        c hR G (insert c s) hexception_countable hGcont hGdiff

/-- Square-contour residue theorem: the rectangular analogue of
`finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue` (`Part13`).

Mathlib supplies the deleted-circle residue theorem directly through
`Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`;
there is no rectangular counterpart, so the square boundary integral is evaluated here by the
residue decomposition `g = (g - residue • (· - c)⁻¹) + residue • (· - c)⁻¹`, using the model
kernel value `2πi`, the linearity split, and the remainder vanishing.

Thin wrapper over the three leaves above. -/
theorem finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue
    (c : ℂ) {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) (residue : ℂ) (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn (fun z : ℂ => (z - c) * g z)
        ((Set.uIcc (c.re - R) (c.re + R) ×ℂ Set.uIcc (c.im - R) (c.im + R)) \ {c}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ ((Set.Ioo (c.re - R) (c.re + R) ×ℂ Set.Ioo (c.im - R) (c.im + R)) \ {c}) \ s →
          DifferentiableAt ℂ (fun w : ℂ => (w - c) * g w) z)
    (hlocal : Tendsto (fun z : ℂ => (z - c) * g z) (𝓝[≠] c) (𝓝 residue)) :
    finiteRectangleSquareBoundaryIntegral g c R =
      (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
  calc
    finiteRectangleSquareBoundaryIntegral g c R =
        finiteRectangleSquareBoundaryIntegral
            (fun z : ℂ => g z - residue • (z - c)⁻¹) c R +
          residue • finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R := by
      exact finiteRectangleSquareBoundaryIntegral_residue_split c hR g residue hcontinuous
    _ = 0 +
          residue • finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R := by
      exact congrArg
        (fun x : ℂ =>
          x + residue • finiteRectangleSquareBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R)
        (finiteRectangleSquareBoundaryIntegral_residueRemainder_eq_zero
          c hR g residue s hs hcontinuous hdifferentiable hlocal)
    _ = 0 + residue • (2 * ↑Real.pi * Complex.I : ℂ) := by
      exact congrArg
        (fun x : ℂ => 0 + residue • x)
        (finiteRectangleSquareBoundaryIntegral_inv_eq_twoPiI c hR)
    _ = residue • (2 * ↑Real.pi * Complex.I : ℂ) := by
      exact zero_add (residue • (2 * ↑Real.pi * Complex.I : ℂ))
    _ = (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
      calc
        residue • (2 * ↑Real.pi * Complex.I : ℂ) =
            residue * (2 * ↑Real.pi * Complex.I : ℂ) := by
          exact Algebra.id.smul_eq_mul residue (2 * ↑Real.pi * Complex.I : ℂ)
        _ = (2 * ↑Real.pi * Complex.I : ℂ) * residue := by
          exact mul_comm residue (2 * ↑Real.pi * Complex.I : ℂ)
        _ = (2 * ↑Real.pi * Complex.I : ℂ) • residue := by
          exact (Algebra.id.smul_eq_mul (2 * ↑Real.pi * Complex.I : ℂ) residue).symm

/-- Sub-sink (coefficient regularity): the simple-pole coefficient `(z - a) * integrand` is
continuous on the punctured closed half-radius disk and quarter-width square, and holomorphic
off the puncture.  This is the meromorphy of the completed explicit-formula integrand near each
raw singular coordinate; it is uniform across the pole coordinates `0`, `1` and the completed
zeros, following from the analytic package `h` and the singular-set characterisation. -/
theorem explicitFormulaRectangleRawSingular_coefficientRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall a (ε / 2) \ {a}) ∧
      (∀ z : ℂ,
        z ∈ (Metric.ball a (ε / 2) \ {a}) \ (∅ : Set ℂ) →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          ((Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
            Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
              Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) := by
  have hεhalf : 0 < ε / 2 :=
    finiteRectangle_halfRadius_pos hε
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b (ε / 2) ⊆ explicitFormulaContourFamilyInterior F T := by
    intro b hb
    exact Set.Subset.trans
      (finiteRectangle_closedBall_subset_of_radius_le
        (finiteRectangle_halfRadius_le_self hε))
      (hclosed b hb)
  have hdisjointHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ d : ℂ,
            d ∈ explicitFormulaRectangleRawSingularCoordinates T →
              b ≠ d →
                Disjoint (Metric.closedBall b (ε / 2)) (Metric.closedBall d (ε / 2)) := by
    intro b hb d hd hbd
    have hhalf_sum :
        ε / 2 + ε / 2 < dist b d := by
      calc
        ε / 2 + ε / 2 = ε := by
          exact add_halves ε
        _ < ε + ε := by
          exact lt_add_of_pos_right ε hε
        _ < dist b d := by
          exact hsep b hb d hd hbd
    exact Metric.closedBall_disjoint_closedBall hhalf_sum
  have hdisk :
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a (ε / 2) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball a (ε / 2) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) :=
    explicitFormulaRectangle_rawDeletedClosedBall_localResidueCoefficient_regular
      f F h hT hεhalf hinterior hclosedHalf hdisjointHalf a ha (∅ : Set ℂ)
  have hsquare_subset_closedBall :
      ((Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
          Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) ⊆
        Metric.closedBall a (ε / 2) \ {a} := by
    intro z hz
    have hzcell :
        z ∈ explicitFormulaRectangleRawInscribedSquareClosedCell (ε / 2) a := by
      have hre :
          z.re ∈
            Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re :=
        finiteRectangle_mem_uIcc_congr_endpoints
          (explicitFormulaRectangleRawInscribedSquareLowerCorner_re (ε / 2) a).symm
          (explicitFormulaRectangleRawInscribedSquareUpperCorner_re (ε / 2) a).symm
          hz.1.1
      have him :
          z.im ∈
            Set.uIcc (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im :=
        finiteRectangle_mem_uIcc_congr_endpoints
          (explicitFormulaRectangleRawInscribedSquareLowerCorner_im (ε / 2) a).symm
          (explicitFormulaRectangleRawInscribedSquareUpperCorner_im (ε / 2) a).symm
          hz.1.2
      exact And.intro hre him
    exact And.intro
      (explicitFormulaRectangleRawInscribedSquareClosedCell_subset_closedBall
        (finiteRectangle_halfRadius_nonneg hε) a hzcell)
      hz.2
  have hcont_square :
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        ((Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
          Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) :=
    hdisk.1.mono hsquare_subset_closedBall
  have hopenSquare_subset_closedBall :
      ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
          Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) ⊆
        Metric.closedBall a (ε / 2) \ {a} := by
    intro z hz
    have hclosedMem :
        z ∈ (Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
          Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) := by
      have hre :
          z.re ∈ Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) := by
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.1.1)
      have him :
          z.im ∈ Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2) := by
        exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hz.1.2)
      exact And.intro hre him
    exact hsquare_subset_closedBall (And.intro hclosedMem hz.2)
  have hregularOpen :
      ContinuousOn
          (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
              Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
              Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) :=
    explicitFormulaRectangle_localResidueCoefficient_regularOn_of_deletedDisk_avoids_singular
      f F h T a
      ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
          Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a})
      (∅ : Set ℂ)
      (fun z hz => hclosedHalf a ha (hopenSquare_subset_closedBall hz).1)
      (fun z hz =>
        explicitFormulaRectangle_deletedClosedBall_not_mem_singularSet_of_rawClosedDisjoint
          F hT hεhalf hinterior hclosedHalf hdisjointHalf ha
          (hopenSquare_subset_closedBall hz))
  exact And.intro hdisk.1
    (And.intro hdisk.2
      (And.intro hcont_square hregularOpen.2))

/-- Sub-sink (residue limit): the simple-pole coefficient `(z - a) * integrand` has a limit at
each raw singular coordinate `a` — the local residue.  By cases this is the proved local
residue limit at the pole coordinates `0`, `1` (the completed-zeta principal parts) and at each
completed zero in the height window (`Part03` local-residue lemmas). -/
theorem explicitFormulaRectangleRawSingular_residueLimit
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ∃ residue : ℂ,
      Tendsto (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] a) (𝓝 residue) := by
  match explicitFormulaRectangleRawSingularCoordinates_cases T ha with
  | Or.inl hzero =>
      let P : ℂ → Prop := fun a₀ : ℂ =>
        ∃ residue : ℂ,
          Tendsto
            (fun z : ℂ => (z - a₀) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] a₀) (𝓝 residue)
      have hzeroCoeff :
          (fun z : ℂ => (z - (0 : ℂ)) * zetaCompletedExplicitFormulaContourIntegrand f z) =
            fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z := by
        funext z
        exact congrArg
          (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f z)
          (sub_zero z)
      have hzeroLimit :
          P (0 : ℂ) :=
        ⟨explicitFormulaRectangle_zeroPoleResidue f,
          Eq.subst
            (motive := fun φ : ℂ → ℂ =>
              Tendsto φ (𝓝[≠] (0 : ℂ)) (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)))
            hzeroCoeff.symm
            (explicitFormulaRectangle_zeroPole_localResidue_tendsto_rawCompleted f h.phi_control)⟩
      exact Eq.subst (motive := P) hzero.symm hzeroLimit
  | Or.inr (Or.inl hone) =>
      let P : ℂ → Prop := fun a₀ : ℂ =>
        ∃ residue : ℂ,
          Tendsto
            (fun z : ℂ => (z - a₀) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] a₀) (𝓝 residue)
      have honeLimit :
          P (1 : ℂ) :=
        ⟨explicitFormulaRectangle_onePoleResidue f,
          explicitFormulaRectangle_onePole_localResidue_tendsto_rawCompleted f h.phi_control⟩
      exact Eq.subst (motive := P) hone.symm honeLimit
  | Or.inr (Or.inr hcompleted) =>
      match hcompleted with
      | ⟨ρ, hρ, hcoord⟩ =>
          let P : ℂ → Prop := fun a₀ : ℂ =>
            ∃ residue : ℂ,
              Tendsto
                (fun z : ℂ => (z - a₀) * zetaCompletedExplicitFormulaContourIntegrand f z)
                (𝓝[≠] a₀) (𝓝 residue)
          have hρLimit :
              P (completedZeroResidueCoordinate ρ) :=
            ⟨explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ),
              explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand
                f h.phi_control ρ⟩
          exact Eq.subst (motive := P) hcoord hρLimit

/-- Sink (analytic-regularity leaf): around each raw singular coordinate the completed
contour integrand, multiplied by `(z - a)`, is continuous on the punctured closed half-radius
disk and quarter-width square, is holomorphic off the puncture, and has a residue limit at `a`.

Thin wrapper: the regularity is the sub-sink
`explicitFormulaRectangleRawSingular_coefficientRegularity` and the residue limit is the sub-sink
`explicitFormulaRectangleRawSingular_residueLimit`. -/
theorem explicitFormulaRectangleRawSingular_puncturedResidueRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ∃ residue : ℂ,
      ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall a (ε / 2) \ {a}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball a (ε / 2) \ {a}) \ (∅ : Set ℂ) →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
        ContinuousOn (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
            ((Set.uIcc (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
              Set.uIcc (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) ∧
          (∀ z : ℂ,
            z ∈ ((Set.Ioo (a.re - (ε / 2) / 2) (a.re + (ε / 2) / 2) ×ℂ
                Set.Ioo (a.im - (ε / 2) / 2) (a.im + (ε / 2) / 2)) \ {a}) \ (∅ : Set ℂ) →
              DifferentiableAt ℂ
                (fun w : ℂ => (w - a) * zetaCompletedExplicitFormulaContourIntegrand f w) z) ∧
            Tendsto (fun z : ℂ => (z - a) * zetaCompletedExplicitFormulaContourIntegrand f z)
              (𝓝[≠] a) (𝓝 residue) := by
  obtain ⟨residue, hlim⟩ :=
    explicitFormulaRectangleRawSingular_residueLimit f F h hT hinterior a ha
  obtain ⟨hcont_disk, hdiff_disk, hcont_square, hdiff_square⟩ :=
    explicitFormulaRectangleRawSingular_coefficientRegularity
      f F h hT hinterior ε hε hclosed hsep a ha
  exact ⟨residue, hcont_disk, hdiff_disk, hcont_square, hdiff_square, hlim⟩

/-- Sink (deformation leaf): around each raw singular coordinate the half-radius deleted
*circle* boundary equals the quarter-width deleted *square* boundary.

This is the genuine planar contour-deformation content: both the circle of radius `ε / 2` and
the square of half-width `(ε / 2) / 2` enclose only the singular coordinate `a`, so by the
deleted-circle and deleted-square residue theorems both equal `2πi` times the same local
residue and hence agree.

Thin wrapper: the residue limit and punctured-disk regularity are supplied by
`explicitFormulaRectangleRawSingular_puncturedResidueRegularity`; the circle value is the
proved deleted-circle residue theorem `finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue`
(`Part13`), and the square value is `finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue`. -/
theorem explicitFormulaRectangleComplement_circleEqDeletedSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
          explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a := by
  intro a ha
  obtain ⟨residue, hcont_circle, hdiff_circle, hcont_square, hdiff_square, hlim⟩ :=
    explicitFormulaRectangleRawSingular_puncturedResidueRegularity
      f F h hT hinterior ε hε hclosed hsep a ha
  have hRhalf : (0 : ℝ) < ε / 2 := half_pos hε
  have hRquarter : (0 : ℝ) < (ε / 2) / 2 := half_pos hRhalf
  have hcircle :
      explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
        (2 * ↑Real.pi * Complex.I : ℂ) • residue :=
    finiteRectangle_deletedCircleIntegral_eq_twoPiI_smul_residue
      (c := a) (R := ε / 2) hRhalf
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) residue
      (∅ : Set ℂ) Set.countable_empty hcont_circle hdiff_circle hlim
  have hsquare :
      explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a =
        (2 * ↑Real.pi * Complex.I : ℂ) • residue :=
    finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue
      a hRquarter
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) residue
      (∅ : Set ℂ) Set.countable_empty hcont_square hdiff_square hlim
  exact Eq.trans hcircle hsquare.symm

/-- Sink (geometric leaf): around each raw singular coordinate the half-radius deleted
*circle* boundary equals the half-radius inscribed *square* boundary.

This is the second conjunct of the regular-grid subdivision hypothesis `hgrid` consumed by
`explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls`.

Thin wrapper: the deleted-square-to-inscribed-square half-width bookkeeping is carried out by
`explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on`
(`Part23`), leaving only the circle-to-deleted-square deformation
`explicitFormulaRectangleComplement_circleEqDeletedSquare`. -/
theorem explicitFormulaRectangleComplement_circleEqSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (ε : ℝ) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
          explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
  explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
    f T ε
    (explicitFormulaRectangleComplement_circleEqDeletedSquare
      f F h hT hinterior ε hε hclosed hsep)

/-- Owner bridge from endpoint-data boundary accounting to the `Finset` regular-cell
subdivision surface.  The endpoint-data layer owns the oriented edge cancellation; this
lemma only folds its list-level boundary sum through the associated duplicate-free
regular-cell list. -/
theorem explicitFormulaRectangleComplement_cellsSubdivision_of_endpointDataBoundarySum_nodup
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)))
    (hnodup :
      (explicitFormulaRectangleRegularGridCellListOfEndpointData data :
        Multiset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2))).Nodup)
    (hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
  exact
    explicitFormulaRectangleRegularGridCellBoundarySum_exists_of_endpointDataBoundarySum_nodup
      f data hnodup hendpoint

/-- Owner bridge from endpoint-data boundary accounting to the `Finset` regular-cell
subdivision surface when duplicate-freeness is available in the constructed
`List.Nodup` form. -/
theorem explicitFormulaRectangleComplement_cellsSubdivision_of_endpointDataBoundarySum_list_nodup
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)))
    (hnodup : data.Nodup)
    (hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
  exact
    explicitFormulaRectangleRegularGridCellBoundarySum_exists_of_endpointDataBoundarySum_list_nodup
      f data hnodup hendpoint

/-- Owner bridge for the canonical selected complement endpoint-data list.  The list is
constructed in `Part17` by filtering crossed adjacent endpoint pairs through the real
coordinate-omission predicate, so the only remaining input here is the endpoint-data
boundary accounting identity. -/
theorem explicitFormulaRectangleComplement_cellsSubdivision_of_selectedEndpointDataBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ}
    (hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2))) :
    ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
  exact
    explicitFormulaRectangleComplement_cellsSubdivision_of_endpointDataBoundarySum_nodup
      f F
      (explicitFormulaRectangleSelectedEndpointData F T (ε / 2))
      (explicitFormulaRectangleSelectedEndpointData_regularGridCellList_nodup
        F T (ε / 2))
      hendpoint

/-- Sub-sink (edge-cancellation core): the raw-hole endpoint-data family has boundary
sum equal to the outer tangent contour minus the inscribed-square hole boundaries.

The owner theorem is the raw-hole endpoint-data edge accounting from `Part20_22`; this
wrapper only converts the grouped edge identity into the endpoint-data boundary-sum
form expected by the finite-hole Cauchy layer. -/
theorem explicitFormulaRectangleComplement_endpointDataSubdivision
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  intro ε hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
  have hT_nonneg : 0 ≤ T :=
    le_of_lt hT
  let data : List
      (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
      (finiteRectangle_halfRadius_pos hε)
  have hedges :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              data) =
        zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData_edgeAccounting_closedRadiusControls
      f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hright hleft
      hrightHole hleftHole hsep
  have hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
          data :=
    explicitFormulaRectangle_tangentContour_sub_rawInscribedSquareCellBoundarySum_eq_endpointDataBoundarySum_of_edgeSums
      f data hedges
  exact ⟨data, hendpoint⟩

/-- Sink (combinatorial leaf): the endpoint-data complement subdivision identity.

Thin wrapper: the endpoint-data family and the `outer − holes` boundary-sum identity are
the edge-cancellation core `explicitFormulaRectangleComplement_endpointDataSubdivision`. -/
theorem explicitFormulaRectangleComplement_subdivisionExists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  intro ε hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
  exact
    explicitFormulaRectangleComplement_endpointDataSubdivision f F h hT hinterior ε hε hclosed
      hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep

/-- The regular-grid subdivision hypothesis `hgrid` of
`explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls`.

Thin wrapper: the subdivision identity is the leaf
`explicitFormulaRectangleComplement_subdivisionExists`, and the circle/inscribed-square
agreement is the proved wrapper `explicitFormulaRectangleComplement_circleEqSquare`. -/
theorem explicitFormulaRectangleComplement_hgrid
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) →
        explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c →
        explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∃ data : List
              (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
            zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  intro ε hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
  exact
    explicitFormulaRectangleComplement_subdivisionExists
      f F h hT hinterior ε hε hclosed hbottom htop hbottomHole htopHole hright hleft
      hrightHole hleftHole hsep

/-- Finite-hole Cauchy–Goursat vanishing for the tangent completed explicit-formula
integrand on the rectangle punctured at the finitely many raw singular coordinates.

For a radius `ε` whose closed `ε`-balls around the raw singular coordinates lie in the open
contour interior and are pairwise separated by more than `2ε`, the tangent contour integral
around the outer rectangle with the `ε`-square holes deleted is zero.  This is the analytic
core of the finite-rectangle residue theorem.

Thin wrapper: the regular-grid subdivision data is supplied by the named sink
`explicitFormulaRectangleComplement_hgrid`, and the per-cell Cauchy–Goursat vanishing is
carried out by `explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_ownerGridSubdivision
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hside :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) ∧
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T ∧
                (∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) ∧
                  (∀ a : ℂ,
                    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) ∧
                    explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c ∧
                      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) ∧
                        (∀ a : ℂ,
                          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
                              (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                (ε / 2) a).re) ∧
                          (∀ a : ℂ,
                            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                              explicitFormulaRectangleSortedYVerticalSideIntegrable f T
                                (ε / 2)
                                (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                  (ε / 2) a).re)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls
      f F h hT hinterior hboundary
      (fun ε hε hclosed hsep =>
        match hside ε hε hclosed hsep with
        | ⟨hbottom, htop, hbottomHole, htopHole, hright, hleft, hrightHole, hleftHole⟩ =>
            explicitFormulaRectangleComplement_hgrid
              f F h hT hinterior hboundary ε hε hclosed hbottom htop hbottomHole htopHole
              hright hleft hrightHole hleftHole hsep)
      (explicitFormulaRectangleComplement_circleEqSquare f F h hT hinterior)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
