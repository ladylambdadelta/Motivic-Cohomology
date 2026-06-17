import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaResidueAccounting

/-!
# Endpoint indentation limits for finite Abel-Plana

This file owns the endpoint semicircle principal-part and remainder estimates,
and the limit identifying deleted boundary indentation contributions with
principal-value endpoint residue terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The left endpoint semicircle has angular length `π`. -/
theorem Real.leftEndpointSemicircle_angleLength :
    Real.pi / 2 - (-(Real.pi / 2)) = Real.pi := by
  exact
    Eq.trans
      (sub_neg_eq_add (Real.pi / 2) (Real.pi / 2))
      (add_halves Real.pi)

/-- The right endpoint semicircle has angular length `π`. -/
theorem Real.rightEndpointSemicircle_angleLength :
    3 * Real.pi / 2 - Real.pi / 2 = Real.pi := by
  have hthree :
      (3 : ℝ) * Real.pi / 2 =
        Real.pi + Real.pi / 2 := by
    calc
      (3 : ℝ) * Real.pi / 2 =
          (Real.pi + Real.pi + Real.pi) / 2 := by
        exact congrArg
          (fun z : ℝ => z / 2)
          (three_mul Real.pi)
      _ = (Real.pi + Real.pi) / 2 + Real.pi / 2 := by
        exact add_div (Real.pi + Real.pi) Real.pi 2
      _ = Real.pi + Real.pi / 2 := by
        exact congrArg
          (fun z : ℝ => z + Real.pi / 2)
          (add_halves Real.pi)
  exact
    Eq.trans
      (congrArg
        (fun z : ℝ => z - Real.pi / 2)
        hthree)
      (add_sub_cancel_right Real.pi (Real.pi / 2))

/-- Cauchy-denominator cancellation along a complex endpoint arc. -/
theorem Complex.div_mul_I_mul_cancel
    (R D : ℂ)
    (hD : D ≠ 0) :
    (R / D) * (Complex.I * D) = Complex.I * R := by
  calc
    (R / D) * (Complex.I * D) =
        (R / D) * (D * Complex.I) := by
      exact congrArg
        (fun z : ℂ => (R / D) * z)
        (mul_comm Complex.I D)
    _ = ((R / D) * D) * Complex.I := by
      exact mul_assoc (R / D) D Complex.I
    _ = R * Complex.I := by
      exact congrArg
        (fun z : ℂ => z * Complex.I)
        (div_mul_cancel₀ R hD)
    _ = Complex.I * R := by
      exact mul_comm R Complex.I

/-- Normalizing a semicircle principal part by `2πi` gives half the residue. -/
theorem Complex.two_pi_I_normalizes_pi_I_to_half
    (R : ℂ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Real.pi : ℂ) * (Complex.I * R)) =
      R / 2 := by
  have hπI :
      (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      Complex.I_ne_zero
  have hnum :
      (Real.pi : ℂ) * (Complex.I * R) =
        R * ((Real.pi : ℂ) * Complex.I) := by
    calc
      (Real.pi : ℂ) * (Complex.I * R) =
          (Real.pi : ℂ) * (R * Complex.I) := by
        exact congrArg
          (fun z : ℂ => (Real.pi : ℂ) * z)
          (mul_comm Complex.I R)
      _ = ((Real.pi : ℂ) * R) * Complex.I := by
        exact mul_assoc (Real.pi : ℂ) R Complex.I
      _ = (R * (Real.pi : ℂ)) * Complex.I := by
        exact congrArg
          (fun z : ℂ => z * Complex.I)
          (mul_comm (Real.pi : ℂ) R)
      _ = R * ((Real.pi : ℂ) * Complex.I) := by
        exact Eq.symm (mul_assoc R (Real.pi : ℂ) Complex.I)
  have hden :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    exact mul_assoc (2 : ℂ) (Real.pi : ℂ) Complex.I
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Real.pi : ℂ) * (Complex.I * R)) =
        ((Real.pi : ℂ) * (Complex.I * R)) /
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      exact inv_mul_eq_div
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        ((Real.pi : ℂ) * (Complex.I * R))
    _ =
        (R * ((Real.pi : ℂ) * Complex.I)) /
          ((2 : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      exact congrArg₂ HDiv.hDiv hnum hden
    _ = R / 2 := by
      exact mul_div_mul_right R (2 : ℂ) hπI

/-- Splitting a removable endpoint numerator into residue plus defect after
arc-denominator transport. -/
theorem Complex.endpointArc_principal_remainder_split
    (R E D : ℂ)
    (hD : D ≠ 0) :
    (D⁻¹ * E) * (Complex.I * D) =
      (R / D) * (Complex.I * D) +
        ((E - R) / D) * (Complex.I * D) := by
  have hdecomp : R + (E - R) = E := by
    calc
      R + (E - R) = (E - R) + R := by
        exact add_comm R (E - R)
      _ = E := by
        exact sub_add_cancel E R
  have hleft :
      (D⁻¹ * E) * (Complex.I * D) = Complex.I * E := by
    calc
      (D⁻¹ * E) * (Complex.I * D) =
          (E / D) * (Complex.I * D) := by
        exact congrArg
          (fun z : ℂ => z * (Complex.I * D))
          (inv_mul_eq_div D E)
      _ = Complex.I * E := by
        exact Complex.div_mul_I_mul_cancel E D hD
  have hright :
      (R / D) * (Complex.I * D) +
          ((E - R) / D) * (Complex.I * D) =
        Complex.I * E := by
    calc
      (R / D) * (Complex.I * D) +
          ((E - R) / D) * (Complex.I * D) =
          Complex.I * R + Complex.I * (E - R) := by
        exact congrArg₂ HAdd.hAdd
          (Complex.div_mul_I_mul_cancel R D hD)
          (Complex.div_mul_I_mul_cancel (E - R) D hD)
      _ = Complex.I * (R + (E - R)) := by
        exact Eq.symm (mul_add Complex.I R (E - R))
      _ = Complex.I * E := by
        exact congrArg (fun z : ℂ => Complex.I * z) hdecomp
  exact hleft.trans hright.symm

/-- Rearrangement of the endpoint-remainder integral majorant product. -/
theorem Real.endpointRemainder_majorant_product_assoc
    (A C L : ℝ) :
    A * (C * L) = A * L * C := by
  calc
    A * (C * L) = A * (L * C) := by
      exact congrArg (fun z : ℝ => A * z) (mul_comm C L)
    _ = A * L * C := by
      exact Eq.symm (mul_assoc A L C)

/-- The endpoint remainder integral majorant with its scale named as `A`. -/
theorem Complex.endpointRemainderIntegral_majorant_as_scale
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ C : ℝ)
    (hρpos : 0 < ρ)
    (hbound :
      ∀ θ ∈ Ι a b,
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ C) :
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
      ≤
        (‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a|) * C := by
  exact
    Complex.norm_endpointSemicircleRemainderIntegral_le
      hw n a b ρ hρpos C hbound

/-- A zero norm is inside every positive ball around zero. -/
theorem Real.zero_norm_mem_ball_of_pos
    {ε x : ℝ}
    (hx : x = 0)
    (hε : 0 < ε) :
    x ∈ Metric.ball (0 : ℝ) ε := by
  have hdist : dist x 0 = 0 := by
    exact congrArg (fun y : ℝ => dist y 0) hx
  exact Metric.mem_ball.mpr
    (Eq.subst
      (motive := fun r : ℝ => r < ε)
      hdist.symm
      hε)

/-- A strict norm bound is exactly membership in the neighborhood ball around
zero. -/
theorem Real.mem_zero_ball_of_lt
    {ε x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (h : x < ε) :
    x ∈ Metric.ball (0 : ℝ) ε := by
  have hdist : dist x 0 = x :=
    Real.dist_norm_to_zero_eq_self hx_nonneg
  exact Metric.mem_ball.mpr
    (Eq.subst
      (motive := fun r : ℝ => r < ε)
      hdist.symm
      h)

/-- Cancelling the positive endpoint-remainder majorant scale. -/
theorem Real.endpointRemainder_scale_cancel
    {A ε : ℝ}
    (hA : A ≠ 0) :
    A * (ε / (2 * A)) = ε / 2 := by
  calc
    A * (ε / (2 * A)) = A * ε / (2 * A) := by
      exact Eq.symm (mul_div_assoc A ε (2 * A))
    _ = ε * A / (2 * A) := by
      exact congrArg
        (fun z : ℝ => z / (2 * A))
        (mul_comm A ε)
    _ = ε / 2 := by
      exact mul_div_mul_right ε (2 : ℝ) hA

/-- Distance from a nonnegative real norm to zero is the norm itself. -/
theorem Real.dist_norm_to_zero_eq_self
    {x : ℝ}
    (hx : 0 ≤ x) :
    dist x 0 = x := by
  have habs : |x| = x := abs_of_nonneg hx
  calc
    dist x 0 = |x - 0| := Real.dist_eq x 0
    _ = |x| := congrArg abs (sub_zero x)
    _ = x := habs

/-- A complex point is in a metric ball when its norm displacement is below
the radius. -/
theorem Complex.mem_ball_of_norm_sub_lt
    {z c : ℂ}
    {δ : ℝ}
    (h : ‖z - c‖ < δ) :
    z ∈ Metric.ball c δ := by
  have hdist : dist z c = ‖z - c‖ := dist_eq_norm z c
  exact Metric.mem_ball.mpr
    (Eq.subst
      (motive := fun r : ℝ => r < δ)
      hdist.symm
      h)

/-- The left endpoint indentation tends to half the local residue at `0`. -/
/-- Pointwise cancellation of the simple-pole principal part along an endpoint
arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hprod : (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    mul_ne_zero hρc hexp
  exact Complex.div_mul_I_mul_cancel
    (Complex.finiteAbelPlanaLogIntegerResidue w n)
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    hprod

/-- The normalized principal-part integral over a positive semicircle is half
the local residue. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integral_eq_halfResidue
    {w : ℂ}
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi)
    {ρ : ℝ}
    (hρ : ρ ≠ 0) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
  have hintegrand :
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (fun _θ : ℝ =>
        Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) := by
    funext θ
    exact
      Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
        n hρ θ
  have hintegral :
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        (b - a : ℝ) •
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) := by
    exact
      Eq.subst
        (motive := fun F : ℝ → ℂ =>
          ∫ θ : ℝ in a..b, F θ =
            (b - a : ℝ) •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n))
        hintegrand.symm
        (intervalIntegral.integral_const
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n))
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ : ℝ in a..b,
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((b - a : ℝ) •
            (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hintegral
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ((Real.pi : ℂ) * (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)) := by
      have hangle_smul :
          (b - a : ℝ) •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) =
            Real.pi •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) :=
        congrArg
          (fun x : ℝ =>
            x • (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n))
          hangle
      have hpi_smul :
          Real.pi •
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) =
            (Real.pi : ℂ) *
              (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) :=
        Complex.real_smul Real.pi
          (Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n)
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        (hangle_smul.trans hpi_smul)
    _ = Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
      exact Complex.two_pi_I_normalizes_pi_I_to_half
        (Complex.finiteAbelPlanaLogIntegerResidue w n)

/-- The principal part of a simple pole contributes half the normalized residue
on a positively oriented semicircle. -/
theorem Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_tendsto_halfResidue
    {w : ℂ}
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi) :
    Tendsto
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) := by
  have hevent :
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ρ : ℝ => Complex.finiteAbelPlanaLogIntegerResidue w n / 2) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρpos
    exact
      Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integral_eq_halfResidue
        n a b hangle (ne_of_gt hρpos)
  exact tendsto_const_nhds.congr' hevent.symm

/-- The endpoint-arc vector has norm exactly the radius. -/
theorem Complex.norm_endpointSemicircleArcVector
    (ρ θ : ℝ) :
    ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = |ρ| := by
  have hcomm :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by
    exact mul_comm Complex.I (θ : ℂ)
  calc
    ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
        ‖(ρ : ℂ)‖ * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact norm_mul (ρ : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
    _ = |ρ| * ‖Complex.exp ((θ : ℂ) * Complex.I)‖ := by
      exact congrArg₂ HMul.hMul
        (RCLike.norm_ofReal ρ)
        (congrArg (fun z : ℂ => ‖Complex.exp z‖) hcomm)
    _ = |ρ| * 1 := by
      exact congrArg
        (fun x : ℝ => |ρ| * x)
        (Complex.norm_exp_ofReal_mul_I θ)
    _ = |ρ| := by
      exact mul_one |ρ|

/-- On a nonzero endpoint arc, the Cauchy denominator cancels against `dz`. -/
theorem Complex.endpointSemicircleRemainder_integrand_eq_I_mul_defect
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) := by
  have hden :
      (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    by
      have hρc : (ρ : ℂ) ≠ 0 := by
        exact Complex.ofReal_ne_zero.mpr hρ
      exact mul_ne_zero hρc (Complex.exp_ne_zero _)
  exact Complex.div_mul_I_mul_cancel
    (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
      ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
      Complex.finiteAbelPlanaLogIntegerResidue w n)
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    hden

/-- The endpoint-arc remainder integrand is bounded by the removable numerator
defect after denominator cancellation. -/
theorem Complex.norm_endpointSemicircleRemainder_integrand_le
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    {C : ℝ}
    {θ : ℝ}
    (hC :
      ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ C) :
    ‖((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ C := by
  calc
    ‖((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n) /
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ =
        ‖Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)‖ := by
      exact congrArg norm
        (Complex.endpointSemicircleRemainder_integrand_eq_I_mul_defect
          n hρ θ)
    _ =
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
        Complex.finiteAbelPlanaLogIntegerResidue w n‖ := by
      calc
        ‖Complex.I *
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)‖ =
            ‖Complex.I‖ *
              ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
          norm_mul Complex.I
            (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n)
        _ =
            1 *
              ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ := by
          exact congrArg
            (fun x : ℝ =>
              x *
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n‖)
            Complex.norm_I
        _ =
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
          one_mul _
    _ ≤ C := hC

/-- The removable regular remainder contributes zero on a shrinking endpoint
semicircle. -/
theorem Complex.norm_endpointSemicircleRemainderIntegral_le
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : 0 < ρ)
    (C : ℝ)
    (hC :
      ∀ θ ∈ Ι a b,
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ C) :
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
      ≤ ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a| * C := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hintegral :
      ‖∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
        ≤ C * |b - a| := by
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun θ hθ =>
        Complex.norm_endpointSemicircleRemainder_integrand_le
          n hρne (hC θ hθ))
  calc
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ =
        ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ *
          ‖∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ := by
      exact norm_mul _ _
    _ ≤ ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (C * |b - a|) := by
      exact mul_le_mul_of_nonneg_left hintegral (norm_nonneg _)
    _ = ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a| * C := by
      exact Real.endpointRemainder_majorant_product_assoc
        ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ C |b - a|

/-- Uniform smallness of the removable numerator on shrinking endpoint arcs. -/
theorem Complex.eventually_endpointSemicircleRemainder_uniform_small
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ θ ∈ Ι a b,
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε := by
  have hcont :
      ContinuousAt
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        (n : ℂ) :=
    Complex.continuousAt_finiteAbelPlanaLogIntegerResidueExtension_at_pole
      hw n
  have hdist :
      ∀ᶠ z : ℂ in 𝓝 (n : ℂ),
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε := by
    have htend :
        Tendsto
          (fun z : ℂ =>
            Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n)
          (𝓝 (n : ℂ))
          (𝓝 0) := by
      have hres :
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) =
            Complex.finiteAbelPlanaLogIntegerResidue w n :=
        Complex.finiteAbelPlana_log_integerResidueExtension_at_pole w n
      have hsub :
          Tendsto
            (fun z : ℂ =>
              Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n)
            (𝓝 (n : ℂ))
            (𝓝
              (Complex.finiteAbelPlanaLogIntegerResidueExtension w n (n : ℂ) -
                Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
        hcont.sub tendsto_const_nhds
      have hlimit_residue_sub :
          Tendsto
            (fun z : ℂ =>
              Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n)
            (𝓝 (n : ℂ))
            (𝓝
              (Complex.finiteAbelPlanaLogIntegerResidue w n -
                Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
        Eq.subst
          (motive := fun L : ℂ =>
            Tendsto
              (fun z : ℂ =>
                Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                  Complex.finiteAbelPlanaLogIntegerResidue w n)
              (𝓝 (n : ℂ))
              (𝓝 (L - Complex.finiteAbelPlanaLogIntegerResidue w n)))
          hres
          hsub
      exact
        Eq.subst
          (motive := fun L : ℂ =>
            Tendsto
              (fun z : ℂ =>
                Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                  Complex.finiteAbelPlanaLogIntegerResidue w n)
              (𝓝 (n : ℂ))
              (𝓝 L))
          (sub_self (Complex.finiteAbelPlanaLogIntegerResidue w n))
          hlimit_residue_sub
    have hnorm :
        Tendsto
          (fun z : ℂ =>
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖)
          (𝓝 (n : ℂ))
          (𝓝 0) := by
      exact htend.norm
    have hevent_dist :
        ∀ᶠ z : ℂ in 𝓝 (n : ℂ),
          dist
            (‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖)
            0 < ε :=
      (Metric.tendsto_nhds.1 hnorm) ε hε
    filter_upwards [hevent_dist] with z hz
    have hnorm_nonneg :
        0 ≤ ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
      norm_nonneg _
    have habs :
        |‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖| =
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
      abs_of_nonneg hnorm_nonneg
    have hlt :
        ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
          Complex.finiteAbelPlanaLogIntegerResidue w n‖ < ε := by
      have hdist_eq :
          dist
              (‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
                Complex.finiteAbelPlanaLogIntegerResidue w n‖)
              0 =
            ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n z -
              Complex.finiteAbelPlanaLogIntegerResidue w n‖ :=
        Real.dist_norm_to_zero_eq_self hnorm_nonneg
      exact
        Eq.subst
          (motive := fun r : ℝ => r < ε)
          hdist_eq
          hz
    exact le_of_lt hlt
  rcases Metric.mem_nhds_iff.1 hdist with ⟨δ, hδpos, hδ⟩
  filter_upwards [self_mem_nhdsWithin,
    (Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hδpos⟩)] with ρ hρpos hρδ θ hθ
  have hnorm_arc :
      ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = ρ := by
    calc
      ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = |ρ| :=
        Complex.norm_endpointSemicircleArcVector ρ θ
      _ = ρ := abs_of_pos hρpos
  have hball :
      (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
        Metric.ball (n : ℂ) δ := by
    apply Complex.mem_ball_of_norm_sub_lt
    calc
      ‖(n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) - (n : ℂ)‖ =
          ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ := by
        exact congrArg norm
          (add_sub_cancel_left (n : ℂ)
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      _ = ρ := hnorm_arc
      _ < δ := hρδ.2
  exact hδ hball

theorem Complex.finiteAbelPlana_log_endpointSemicircleRemainder_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ) :
    Tendsto
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (by
      refine Metric.tendsto_nhds.2 ?_
      intro ε hε
      let A : ℝ := ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹‖ * |b - a|
      have hAnonneg : 0 ≤ A := by
        exact mul_nonneg (norm_nonneg _) (abs_nonneg _)
      by_cases hAzero : A = 0
      · have hsmall :
            ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
              ∀ θ ∈ Ι a b,
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ 1 :=
          Complex.eventually_endpointSemicircleRemainder_uniform_small
            hw n a b zero_lt_one
        filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρpos hbound
        have hle :
            ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                ∫ θ : ℝ in a..b,
                  ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n) /
                      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                    (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
              ≤ A * 1 := by
          exact
            Complex.endpointRemainderIntegral_majorant_as_scale
              hw n a b ρ hρpos 1 hbound
        have hzero_le :
            ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                ∫ θ : ℝ in a..b,
                  ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n) /
                      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                    (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
              = 0 := by
          have hA_one_zero : A * 1 = 0 := by
            exact congrArg (fun x : ℝ => x * 1) hAzero
          have hle_zero :
              ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  ∫ θ : ℝ in a..b,
                    ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                        Complex.finiteAbelPlanaLogIntegerResidue w n) /
                        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                ≤ 0 :=
            Eq.subst
              (motive := fun r : ℝ =>
                ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                    ∫ θ : ℝ in a..b,
                      ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                          Complex.finiteAbelPlanaLogIntegerResidue w n) /
                          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
                  ≤ r)
              hA_one_zero
              hle
          exact le_antisymm hle_zero (norm_nonneg _)
        exact Real.zero_norm_mem_ball_of_pos hzero_le hε
      · have hApos : 0 < A := lt_of_le_of_ne hAnonneg (Ne.symm hAzero)
        have hsmall :
            ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
              ∀ θ ∈ Ι a b,
                ‖Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n‖ ≤ ε / (2 * A) :=
          Complex.eventually_endpointSemicircleRemainder_uniform_small
            hw n a b (div_pos hε (mul_pos two_pos hApos))
        filter_upwards [self_mem_nhdsWithin, hsmall] with ρ hρpos hbound
        have hle :
            ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                ∫ θ : ℝ in a..b,
                  ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n) /
                    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                    (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
              ≤ A * (ε / (2 * A)) := by
          exact
            Complex.endpointRemainderIntegral_majorant_as_scale
              hw n a b ρ hρpos (ε / (2 * A)) hbound
        have hA_cancel : A * (ε / (2 * A)) = ε / 2 := by
          exact Real.endpointRemainder_scale_cancel (ne_of_gt hApos)
        have hhalf_lt : ε / 2 < ε := by
          exact half_lt_self hε
        have hlt :
            ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                ∫ θ : ℝ in a..b,
                  ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                        ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                      Complex.finiteAbelPlanaLogIntegerResidue w n) /
                      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                    (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖
              < ε := by
          exact lt_of_le_of_lt (hA_cancel ▸ hle) hhalf_lt
        exact Real.mem_zero_ball_of_lt (norm_nonneg _) hlt)
/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircle_integrand_eq_principal_add_remainder
    (w : ℂ)
    (n : ℕ)
    (ρ : ℝ)
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
      ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hden :
      (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 :=
    mul_ne_zero hρc hexp
  have hpoint_ne :
      (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ (n : ℂ) := by
    intro h
    have hzero :
        (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) = 0 := by
      exact add_left_cancel h
    exact hden hzero
  have hrewrite :
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    have hoff :
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          (((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
      Complex.finiteAbelPlana_log_integerResidueExtension_eq_centered_off_pole
        w n hpoint_ne
    calc
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        1 * Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact (one_mul _).symm
      _ =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun u : ℂ =>
            u * Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (inv_mul_cancel₀ hden).symm
      _ =
        (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          (((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ))) *
          Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun z : ℂ =>
            (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ * z) *
              Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (Eq.symm
            (add_sub_cancel_left (n : ℂ)
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))))
      _ =
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          ((((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)) *
            Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
        exact mul_assoc _ _ _
      _ =
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
        exact congrArg
          (fun u : ℂ => ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ * u)
          hoff.symm
  calc
    Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹ *
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      exact congrArg
        (fun z : ℂ => z * (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        hrewrite
    _ =
      ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
      ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n) /
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      exact Complex.endpointArc_principal_remainder_split
        (Complex.finiteAbelPlanaLogIntegerResidue w n)
        (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        hden

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIntegral_linearized
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : ρ ≠ 0)
    (hprincipal :
      IntervalIntegrable
        (fun θ : ℝ =>
          ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume a b)
    (hremainder :
      IntervalIntegrable
        (fun θ : ℝ =>
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        volume a b) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          (Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hpoint :
      (fun θ : ℝ =>
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    funext θ
    exact
      Complex.finiteAbelPlana_log_endpointSemicircle_integrand_eq_principal_add_remainder
        w n ρ hρ θ
  have hintegral :
      ∫ θ : ℝ in a..b,
        (Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ∫ θ : ℝ in a..b,
        (((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    exact congrArg (fun f : ℝ → ℂ => ∫ θ : ℝ in a..b, f θ) hpoint
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          (Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          (((Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
          ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
              Complex.finiteAbelPlanaLogIntegerResidue w n) /
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
      exact congrArg
        (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
        hintegral
    _ =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      have hintegral_add :
          ∫ θ : ℝ in a..b,
            (((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          (∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
          (∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
        intervalIntegral.integral_add hprincipal hremainder
      calc
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ : ℝ in a..b,
              (((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
              ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ((∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
            (∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
          exact congrArg
            (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
            hintegral_add
        _ =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              ∫ θ : ℝ in a..b,
                ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                  (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              ∫ θ : ℝ in a..b,
                ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                      ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                    Complex.finiteAbelPlanaLogIntegerResidue w n) /
                    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                  (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
          mul_add
            (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
            (∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            (∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.intervalIntegrable_endpointSemicirclePrincipalPart
    (w : ℂ)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρ : ρ ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      volume a b := by
  have hpoint :
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (fun _θ : ℝ =>
        Complex.I * Complex.finiteAbelPlanaLogIntegerResidue w n) := by
    funext θ
    exact
      Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_integrand_eq_const
        n hρ θ
  exact
    Eq.subst
      (motive := fun F : ℝ → ℂ => IntervalIntegrable F volume a b)
      hpoint.symm
      intervalIntegrable_const

/-- The removable endpoint-arc remainder integrand is interval-integrable for
each nonzero radius. -/
theorem Complex.continuous_endpointSemicircleArc
    (n : ℕ)
    (ρ : ℝ) :
    Continuous
      (fun θ : ℝ =>
        (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  -- Continuity of `θ ↦ n + ρ exp(iθ)`.
  continuity

/-- The nonzero-radius endpoint arc vector never vanishes. -/
theorem Complex.endpointSemicircleArcVector_ne_zero
    {ρ : ℝ}
    (hρ : ρ ≠ 0)
    (θ : ℝ) :
    (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := by
  have hρc : (ρ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hρ
  exact mul_ne_zero hρc (Complex.exp_ne_zero _)

/-- A sufficiently small positive endpoint arc stays inside the residue
isolation ball around its center. -/
theorem Complex.endpointSemicircleArc_mem_integerResidueIsolationBall
    {w : ℂ}
    (n : ℕ)
    {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (θ : ℝ) :
    (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      Metric.ball (n : ℂ)
        (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
  have hdist :
      dist ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (n : ℂ) =
        ρ := by
    calc
      dist ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (n : ℂ) =
          ‖((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - (n : ℂ)‖ := by
        exact dist_eq_norm _ _
      _ = ‖(ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ := by
        exact congrArg norm
          (add_sub_cancel_left (n : ℂ)
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      _ = |ρ| := Complex.norm_endpointSemicircleArcVector ρ θ
      _ = ρ := abs_of_pos hρpos
  exact hdist ▸ hρR

/-- The removable numerator extension is continuous along a nonzero endpoint
arc. -/
theorem Complex.continuousOn_endpointSemicircleResidueExtension_comp_arc
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ContinuousOn
      (fun θ : ℝ =>
        Complex.finiteAbelPlanaLogIntegerResidueExtension w n
          ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (uIcc a b) := by
  let arc : ℝ → ℂ :=
    fun θ : ℝ =>
      (n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have harc_continuous : Continuous arc :=
    Complex.continuous_endpointSemicircleArc n ρ
  have hresidue_continuous :
      ContinuousOn
        (fun z : ℂ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n z)
        (Metric.ball (n : ℂ)
          (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)) :=
    (Complex.differentiableOn_finiteAbelPlanaLogIntegerResidueExtension_isolationBall
      hw n).continuousOn
  have harc_maps :
      ∀ θ ∈ uIcc a b,
        arc θ ∈ Metric.ball (n : ℂ)
          (Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) := by
    intro θ _hθ
    exact
      Complex.endpointSemicircleArc_mem_integerResidueIsolationBall
        n hρpos hρR θ
  exact hresidue_continuous.comp harc_continuous.continuousOn harc_maps

/-- The removable endpoint-arc remainder integrand is continuous on the angle
interval. -/
theorem Complex.continuousOn_endpointSemicircleRemainderIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ContinuousOn
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (uIcc a b) := by
  have hnum :
      ContinuousOn
        (fun θ : ℝ =>
          Complex.finiteAbelPlanaLogIntegerResidueExtension w n
            ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
          Complex.finiteAbelPlanaLogIntegerResidue w n)
        (uIcc a b) :=
    (Complex.continuousOn_endpointSemicircleResidueExtension_comp_arc
      hw n a b ρ hρpos hρR).sub continuousOn_const
  have hden :
      ContinuousOn
        (fun θ : ℝ =>
          (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (uIcc a b) := by
    exact (Complex.continuous_endpointSemicircleArc 0 ρ).sub continuousOn_const
  have hquot :
      ContinuousOn
        (fun θ : ℝ =>
          (Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (uIcc a b) :=
    have hρne : ρ ≠ 0 := ne_of_gt hρpos
    hnum.div hden (fun θ _hθ =>
      Complex.endpointSemicircleArcVector_ne_zero hρne θ)
  have hdz :
      ContinuousOn
        (fun θ : ℝ =>
          Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (uIcc a b) := by
    continuity
  exact hquot.mul hdz

/-- The removable endpoint-arc remainder integrand is interval-integrable for
each nonzero radius. -/
theorem Complex.intervalIntegrable_endpointSemicircleRemainder
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    IntervalIntegrable
      (fun θ : ℝ =>
        ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
            Complex.finiteAbelPlanaLogIntegerResidue w n) /
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      volume a b := by
  exact
    (Complex.continuousOn_endpointSemicircleRemainderIntegrand
      hw n a b ρ hρpos hρR).intervalIntegrable

/-- Endpoint arc decomposition into the principal simple-pole part plus the
removable regular remainder after integrating over the arc. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIntegral_eq_principal_add_remainder
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρR : ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ : ℝ in a..b,
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                  ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                Complex.finiteAbelPlanaLogIntegerResidue w n) /
                ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  -- Pointwise Laurent decomposition, followed by linearity of the interval
  -- integral and multiplication by the normalization constant.
  exact
    Complex.finiteAbelPlana_log_endpointSemicircleIntegral_linearized
      w n a b ρ (ne_of_gt hρpos)
      (Complex.intervalIntegrable_endpointSemicirclePrincipalPart
        w n a b ρ (ne_of_gt hρpos))
      (Complex.intervalIntegrable_endpointSemicircleRemainder
        hw n a b ρ hρpos hρR)

/-- Local half-arc residue theorem for an integer cotangent pole.

The removable numerator is already owned by
`finiteAbelPlanaLogIntegerResidueExtension`; this theorem is the endpoint
version of the existing full-circle residue theorem.  The interval endpoints
are required to differ by `π`, so the principal part contributes exactly half
of the normalized residue. -/
theorem Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re)
    (n : ℕ)
    (a b : ℝ)
    (hangle : b - a = Real.pi) :
    Tendsto
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) := by
  have hprincipal :
      Tendsto
        (fun ρ : ℝ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n / 2)) :=
    Complex.finiteAbelPlana_log_endpointSemicirclePrincipalPart_tendsto_halfResidue
      n a b hangle
  have hremainder :
      Tendsto
        (fun ρ : ℝ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_endpointSemicircleRemainder_tendsto_zero
      hw n a b
  have hsum := hprincipal.add hremainder
  have hpoint :
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∫ θ : ℝ in a..b,
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) +
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ : ℝ in a..b,
              ((Complex.finiteAbelPlanaLogIntegerResidueExtension w n
                    ((n : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) -
                  Complex.finiteAbelPlanaLogIntegerResidue w n) /
                  ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) *
                (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
    filter_upwards
      [Complex.eventually_pos_lt_finiteAbelPlanaLogIntegerResidueIsolationRadius
        hw n] with ρ hρ
    exact
      Complex.finiteAbelPlana_log_endpointSemicircleIntegral_eq_principal_add_remainder
        hw n a b ρ hρ.1 hρ.2
  have htarget :
      Complex.finiteAbelPlanaLogIntegerResidue w n / 2 + 0 =
        Complex.finiteAbelPlanaLogIntegerResidue w n / 2 := by
    exact add_zero _
  exact (htarget ▸ hsum).congr' hpoint.symm

/-- The left endpoint indentation tends to half the local residue at `0`. -/
theorem Complex.finiteAbelPlana_log_leftEndpointIndentationIntegral_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2)) := by
  exact
    Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
      hw 0 (-(Real.pi / 2)) (Real.pi / 2)
      Real.leftEndpointSemicircle_angleLength

/-- The right endpoint indentation tends to half the local residue at `N + 1`. -/
theorem Complex.finiteAbelPlana_log_rightEndpointIndentationIntegral_tendsto_halfResidue
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) := by
  exact
    Complex.finiteAbelPlana_log_endpointSemicircleIndentation_tendsto_halfResidue
      hw (N + 1) (Real.pi / 2) (3 * Real.pi / 2)
      Real.rightEndpointSemicircle_angleLength

/-- Unfolding of the interior integer residue contribution. -/
theorem Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w =
      ∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogIntegerResidue w (n + 1) :=
  rfl

/-- Unfolding of the endpoint half-residue contribution. -/
theorem Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
      (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 :=
  rfl

/-- Unfolding of the finite-radius deleted-boundary contribution. -/
theorem Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution_unfold
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
        Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ :=
  rfl

/-- Unfolding of the principal-value integer residue contribution. -/
theorem Complex.finiteAbelPlanaLogPVIntegerResidueContribution_unfold
    (N : ℕ)
    (w : ℂ) :
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
        Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
  rfl

/-- The finite-radius deleted-boundary contribution converges to the
principal-value residue contribution. -/
theorem Complex.finiteAbelPlana_log_pvDeletedBoundaryIntegralContribution_tendsto_pvResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hleft :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2)) :=
    Complex.finiteAbelPlana_log_leftEndpointIndentationIntegral_tendsto_halfResidue
      hw
  have hright :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2)) :=
    Complex.finiteAbelPlana_log_rightEndpointIndentationIntegral_tendsto_halfResidue
      hw N
  have hinterior :
      Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) := by
    have hlocal :
        ∀ n ∈ Finset.range N,
          Tendsto
            (fun ρ : ℝ =>
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)
            (𝓝[>] (0 : ℝ))
            (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (n + 1))) :=
      fun n _hn =>
        Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
          hw (n + 1)
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun ρ : ℝ =>
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                  w (n + 1 : ℂ) ρ)
            (𝓝[>] (0 : ℝ))
            (𝓝 z))
        (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution_unfold N w).symm
        (tendsto_finset_sum (Finset.range N) hlocal)
  have hendpoints :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
            Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)) := by
    have hsum := hleft.add hright
    have htarget :
        Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2 =
          Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w := by
      calc
        Complex.finiteAbelPlanaLogIntegerResidue w 0 / 2 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1) / 2 =
          (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 :=
          (add_div
            (Complex.finiteAbelPlanaLogIntegerResidue w 0)
            (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))
            (2 : ℂ)).symm
        _ = Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w :=
          (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution_unfold N w).symm
    exact htarget ▸ hsum
  have htotal := hendpoints.add hinterior
  have hsource :
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ) =
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
          Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
            ∑ n in Finset.range N,
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                w (n + 1 : ℂ) ρ) := by
    funext ρ
    exact Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution_unfold N w ρ
  have htarget :
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w =
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution_unfold N w
  exact
    Eq.subst
      (motive := fun F : ℝ → ℂ =>
        Tendsto F (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)))
      hsource.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun ρ : ℝ =>
              Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ +
                Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ +
                  ∑ n in Finset.range N,
                    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                      w (n + 1 : ℂ) ρ)
            (𝓝[>] (0 : ℝ))
            (𝓝 z))
        htarget.symm
        htotal)

end

end LFunctions
end Boundary
