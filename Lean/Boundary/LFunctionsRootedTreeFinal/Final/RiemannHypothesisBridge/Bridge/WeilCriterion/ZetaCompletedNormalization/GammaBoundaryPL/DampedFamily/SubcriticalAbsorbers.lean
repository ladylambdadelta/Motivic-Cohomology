import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.HolomorphyAndBarriers
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.BoundedHeightRectangle
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.FiniteOrderEnvelope

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- Upper-tail scalar absorber for the subcritical cosine damping estimate. -/
def verticalStripSubcriticalCosineUpperAbsorber
    (a b d ε y : ℝ) : ℝ :=
  Real.exp
    (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
      Real.exp (d * y)))

/-- Top-edge lower-bound scalar for the subcritical cosine barrier. -/
def verticalStripSubcriticalCosineTopEdgeBarrierLower
    (a b d y : ℝ) : ℝ :=
  (Real.cos (d * ((b - a) / 2)) / 2) *
    Real.exp (d * y)

/-- Top-edge scalar bound for the subcritical cosine damping factor. -/
def verticalStripSubcriticalCosineDampingFactorTopEdgeBound
    (a b d ε y : ℝ) : ℝ :=
  Real.exp
    (-(ε * verticalStripSubcriticalCosineTopEdgeBarrierLower a b d y))

/-- Norm of the scalar subcritical cosine damping factor. -/
def verticalStripSubcriticalCosineDampingFactorNorm
    (a b d ε : ℝ)
    (z : ℂ) : ℝ :=
  ‖Complex.exp
    (-((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z)‖

/-- Product bound used by the top-edge subcritical damping estimate. -/
def verticalStripSubcriticalCosineTopEdgePreAbsorptionBound
    (a b c d D ε K y : ℝ) : ℝ :=
  (K * Real.exp (D * Real.exp (c * y))) *
    verticalStripSubcriticalCosineDampingFactorTopEdgeBound a b d ε y

/-- Real part of the subcritical cosine-damping exponent. -/
theorem verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul
    (a b d ε : ℝ)
    (z : ℂ) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  calc
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        (-ε) * (verticalStripSubcriticalCosineBarrierKernel a b d z).re -
          (0 : ℝ) * (verticalStripSubcriticalCosineBarrierKernel a b d z).im := by
      exact
        Eq.trans
          (Complex.mul_re
            (-((ε : ℝ) : ℂ))
            (verticalStripSubcriticalCosineBarrierKernel a b d z))
          (congrArg₂
            (fun x y : ℝ =>
              x * (verticalStripSubcriticalCosineBarrierKernel a b d z).re -
                y * (verticalStripSubcriticalCosineBarrierKernel a b d z).im)
            (by
              calc
                (-((ε : ℝ) : ℂ)).re = -(((ε : ℝ) : ℂ).re) :=
                  Complex.neg_re ((ε : ℝ) : ℂ)
                _ = -ε :=
                  congrArg Neg.neg (Complex.ofReal_re ε))
            (by
              calc
                (-((ε : ℝ) : ℂ)).im = -(((ε : ℝ) : ℂ).im) :=
                  Complex.neg_im ((ε : ℝ) : ℂ)
                _ = -0 :=
                  congrArg Neg.neg (Complex.ofReal_im ε)
                _ = 0 :=
                  neg_zero))
    _ = (-ε) * (verticalStripSubcriticalCosineBarrierKernel a b d z).re - 0 := by
      exact congrArg
        (fun x : ℝ =>
          (-ε) * (verticalStripSubcriticalCosineBarrierKernel a b d z).re - x)
        (zero_mul (verticalStripSubcriticalCosineBarrierKernel a b d z).im)
    _ = (-ε) * (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
      exact sub_zero
        ((-ε) * (verticalStripSubcriticalCosineBarrierKernel a b d z).re)
    _ = -(ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re) := by
      exact neg_mul ε (verticalStripSubcriticalCosineBarrierKernel a b d z).re
    _ = -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
      exact (neg_mul ε (verticalStripSubcriticalCosineBarrierKernel a b d z).re).symm

/-- Exponentiating a lower bound for the barrier real part gives the matching
upper bound for the damping factor. -/
theorem verticalStripSubcriticalCosineDampingFactor_norm_le_exp_neg_of_re_lower
    {a b d ε L : ℝ}
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hL :
      L ≤ (verticalStripSubcriticalCosineBarrierKernel a b d z).re) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp (-(ε * L)) := by
  let K : ℂ := verticalStripSubcriticalCosineBarrierKernel a b d z
  let w : ℂ := -((ε : ℝ) : ℂ) * K
  have hre :
      w.re = -ε * K.re := by
    exact
      verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hmul_le : ε * L ≤ ε * K.re :=
    mul_le_mul_of_nonneg_left hL hε
  have hneg_le : -(ε * K.re) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have harg_eq : -ε * K.re = -(ε * K.re) :=
    neg_mul ε K.re
  have hre_le : w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ -(ε * L))
      (Eq.trans hre harg_eq).symm
      hneg_le
  have hexp_le : Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ Real.exp (-(ε * L)))
      hnorm.symm
      hexp_le

/-- The subcritical damped family norm factors into the original norm times the
scalar damping factor norm. -/
theorem verticalStripSubcriticalCosineDampedFamily_norm_eq_mul_dampingNorm
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (z : ℂ) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
      ‖f z‖ *
        verticalStripSubcriticalCosineDampingFactorNorm a b d ε z := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  calc
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z * g‖ := by
      rfl
    _ = ‖f z‖ * ‖g‖ := by
      exact norm_mul (f z) g

/-- Top-edge lower bound for the cosine barrier converted to the scalar
damping-factor estimate. -/
theorem verticalStripSubcriticalCosineDampingFactor_topEdge_norm_le
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    verticalStripSubcriticalCosineDampingFactorNorm a b d ε z ≤
      verticalStripSubcriticalCosineDampingFactorTopEdgeBound a b d ε z.im := by
  have hL :
      verticalStripSubcriticalCosineTopEdgeBarrierLower a b d z.im ≤
        (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_closedStrip_re_ge_exp
      hab hd_pos hd_threshold hza hzb
  exact
    verticalStripSubcriticalCosineDampingFactor_norm_le_exp_neg_of_re_lower
      hε hL

/-- Multiplying the function envelope by the scalar top-edge damping estimate. -/
theorem verticalStripSubcriticalCosineTopEdge_mul_envelope_le_bound
    {a b c d D ε K : ℝ}
    {z : ℂ}
    {f : ℂ → ℂ}
    (hf : ‖f z‖ ≤ K * Real.exp (D * Real.exp (c * z.im)))
    (hg :
      verticalStripSubcriticalCosineDampingFactorNorm a b d ε z ≤
        verticalStripSubcriticalCosineDampingFactorTopEdgeBound a b d ε z.im) :
    ‖f z‖ *
        verticalStripSubcriticalCosineDampingFactorNorm a b d ε z ≤
      verticalStripSubcriticalCosineTopEdgePreAbsorptionBound
        a b c d D ε K z.im := by
  let gnorm : ℝ :=
    verticalStripSubcriticalCosineDampingFactorNorm a b d ε z
  let envelope : ℝ := K * Real.exp (D * Real.exp (c * z.im))
  let absorber : ℝ :=
    verticalStripSubcriticalCosineDampingFactorTopEdgeBound a b d ε z.im
  have hgnorm_nonneg : 0 ≤ gnorm :=
    norm_nonneg
      (Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z))
  have hfirst : ‖f z‖ * gnorm ≤ envelope * gnorm :=
    mul_le_mul_of_nonneg_right hf hgnorm_nonneg
  have henvelope_nonneg : 0 ≤ envelope :=
    le_trans (norm_nonneg (f z)) hf
  have hsecond : envelope * gnorm ≤ envelope * absorber :=
    mul_le_mul_of_nonneg_left hg henvelope_nonneg
  exact le_trans hfirst hsecond

/-- Top-edge pointwise estimate for the subcritical cosine-damped family,
before the scalar `c < d` absorption step. -/
theorem verticalStripSubcriticalCosineDampedFamily_topEdge_preAbsorption
    (f : ℂ → ℂ)
    {a b c d D ε K : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hf :
      ‖f z‖ ≤ K * Real.exp (D * Real.exp (c * z.im))) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      verticalStripSubcriticalCosineTopEdgePreAbsorptionBound
        a b c d D ε K z.im := by
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ *
          verticalStripSubcriticalCosineDampingFactorNorm a b d ε z :=
    verticalStripSubcriticalCosineDampedFamily_norm_eq_mul_dampingNorm
      f a b d ε z
  have hfactor :
      verticalStripSubcriticalCosineDampingFactorNorm a b d ε z ≤
        verticalStripSubcriticalCosineDampingFactorTopEdgeBound a b d ε z.im :=
    verticalStripSubcriticalCosineDampingFactor_topEdge_norm_le
      hab hd_pos hd_threshold hε hza hzb
  have hproduct :
      ‖f z‖ *
          verticalStripSubcriticalCosineDampingFactorNorm a b d ε z ≤
        verticalStripSubcriticalCosineTopEdgePreAbsorptionBound
          a b c d D ε K z.im :=
    verticalStripSubcriticalCosineTopEdge_mul_envelope_le_bound
      hf hfactor
  exact
    (Eq.subst
      (motive := fun y : ℝ =>
        y ≤ verticalStripSubcriticalCosineTopEdgePreAbsorptionBound
          a b c d D ε K z.im)
      hnorm_mul.symm
      hproduct)

/-- A lower-rate double exponential is eventually absorbed by a higher-rate
double-exponential damping term. -/
theorem doubleExponential_exp_mul_subcritical_absorber_eventually_le_const
    {K D L c d ε : ℝ}
    (hK : 0 < K)
    (hL : 0 < L)
    (hε : 0 < ε)
    (hcd : c < d) :
    ∀ᶠ T : ℝ in Filter.atTop,
      K * Real.exp (D * Real.exp (c * T)) *
          Real.exp (-(ε * L * Real.exp (d * T))) ≤ K := by
  let E : ℝ := ε * L
  have hE_pos : 0 < E :=
    mul_pos hε hL
  have hdiff_pos : 0 < d - c :=
    sub_pos.mpr hcd
  have htendsto :
      Filter.Tendsto (fun T : ℝ => Real.exp ((d - c) * T))
        Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hdiff_pos Filter.tendsto_id)
  have heventual :
      ∀ᶠ T : ℝ in Filter.atTop,
        D / E ≤ Real.exp ((d - c) * T) :=
    (Filter.tendsto_atTop.mp htendsto) (D / E)
  exact
    heventual.mono
      fun T hT =>
        have hE_nonneg : 0 ≤ E :=
          le_of_lt hE_pos
        have hD_le :
            D ≤ E * Real.exp ((d - c) * T) := by
          have hscaled :
              E * (D / E) ≤ E * Real.exp ((d - c) * T) :=
            mul_le_mul_of_nonneg_left hT hE_nonneg
          have hcancel :
              E * (D / E) = D := by
            calc
              E * (D / E) = E * (D * E⁻¹) := by
                exact congrArg (fun x : ℝ => E * x) (div_eq_mul_inv D E)
              _ = E * (E⁻¹ * D) := by
                exact congrArg (fun x : ℝ => E * x) (mul_comm D E⁻¹)
              _ = (E * E⁻¹) * D := by
                exact (mul_assoc E E⁻¹ D).symm
              _ = 1 * D := by
                exact congrArg (fun x : ℝ => x * D)
                  (mul_inv_cancel₀ (ne_of_gt hE_pos))
              _ = D := one_mul D
          exact
            Eq.subst
              (motive := fun x : ℝ => x ≤ E * Real.exp ((d - c) * T))
              hcancel
              hscaled
        have hexp_c_pos : 0 < Real.exp (c * T) :=
          Real.exp_pos (c * T)
        have hmul_le :
            D * Real.exp (c * T) ≤
              (E * Real.exp ((d - c) * T)) * Real.exp (c * T) :=
          mul_le_mul_of_nonneg_right hD_le (le_of_lt hexp_c_pos)
        have hrate :
            (E * Real.exp ((d - c) * T)) * Real.exp (c * T) =
              E * Real.exp (d * T) := by
          calc
            (E * Real.exp ((d - c) * T)) * Real.exp (c * T) =
                E * (Real.exp ((d - c) * T) * Real.exp (c * T)) :=
              mul_assoc E (Real.exp ((d - c) * T)) (Real.exp (c * T))
            _ = E * Real.exp (((d - c) * T) + c * T) := by
              exact congrArg (fun x : ℝ => E * x)
                (Real.exp_add ((d - c) * T) (c * T)).symm
            _ = E * Real.exp (d * T) := by
              have harg :
                  ((d - c) * T) + c * T = d * T := by
                calc
                  ((d - c) * T) + c * T =
                      ((d - c) + c) * T := by
                    exact (add_mul (d - c) c T).symm
                  _ = d * T := by
                    exact congrArg (fun x : ℝ => x * T) (sub_add_cancel d c)
              exact congrArg (fun x : ℝ => E * Real.exp x) harg
        have hexponent_le :
            D * Real.exp (c * T) ≤ E * Real.exp (d * T) :=
          Eq.subst
            (motive := fun x : ℝ => D * Real.exp (c * T) ≤ x)
            hrate
            hmul_le
        have hsum_nonpos :
            D * Real.exp (c * T) + -(E * Real.exp (d * T)) ≤ 0 := by
          calc
            D * Real.exp (c * T) + -(E * Real.exp (d * T)) ≤
                E * Real.exp (d * T) + -(E * Real.exp (d * T)) :=
              add_le_add_right hexponent_le (-(E * Real.exp (d * T)))
            _ = 0 :=
              add_neg_cancel (E * Real.exp (d * T))
        have hexp_le_one :
            Real.exp (D * Real.exp (c * T) + -(E * Real.exp (d * T))) ≤ 1 :=
          Real.exp_le_one_iff.mpr hsum_nonpos
        have hinner_eq :
            Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(ε * L * Real.exp (d * T))) =
              Real.exp (D * Real.exp (c * T) + -(E * Real.exp (d * T))) := by
          have hE_arg :
              ε * L * Real.exp (d * T) = E * Real.exp (d * T) := rfl
          calc
            Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(ε * L * Real.exp (d * T))) =
              Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(E * Real.exp (d * T))) := by
                exact congrArg
                  (fun x : ℝ =>
                    Real.exp (D * Real.exp (c * T)) * Real.exp (-x))
                  hE_arg
            _ =
              Real.exp (D * Real.exp (c * T) + -(E * Real.exp (d * T))) :=
              (Real.exp_add
                (D * Real.exp (c * T))
                (-(E * Real.exp (d * T)))).symm
        have hinner_le :
            Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(ε * L * Real.exp (d * T))) ≤ 1 :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ 1)
            hinner_eq.symm
            hexp_le_one
        have hscaled :
            K *
                (Real.exp (D * Real.exp (c * T)) *
                  Real.exp (-(ε * L * Real.exp (d * T)))) ≤
              K * 1 :=
          mul_le_mul_of_nonneg_left hinner_le (le_of_lt hK)
        have hleft_assoc :
            K * Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(ε * L * Real.exp (d * T))) =
              K *
                (Real.exp (D * Real.exp (c * T)) *
                  Real.exp (-(ε * L * Real.exp (d * T)))) :=
          mul_assoc K
            (Real.exp (D * Real.exp (c * T)))
            (Real.exp (-(ε * L * Real.exp (d * T))))
        have hright_one : K * 1 = K :=
          mul_one K
        Eq.subst
          (motive := fun x : ℝ =>
            K * Real.exp (D * Real.exp (c * T)) *
                Real.exp (-(ε * L * Real.exp (d * T))) ≤ x)
          hright_one
          (Eq.subst
            (motive := fun x : ℝ => x ≤ K * 1)
            hleft_assoc.symm
            hscaled)

/-- On the right boundary ray, the subcritical barrier real part has
exponential lower growth in the lower-tail height. -/
theorem verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_exp_neg
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = b) :
    (Real.cos (d * ((b - a) / 2)) / 2) * Real.exp (-(d * z.im)) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * ((b - a) / 2))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_lower :
      Real.exp (-(d * z.im)) / 2 ≤ Real.cosh (d * z.im) :=
    real_exp_neg_half_le_cosh (d * z.im)
  have hmul_lower :
      c * (Real.exp (-(d * z.im)) / 2) ≤ c * Real.cosh (d * z.im) :=
    mul_le_mul_of_nonneg_left hcosh_lower hc_nonneg
  have hleft_eq :
      (c / 2) * Real.exp (-(d * z.im)) =
        c * (Real.exp (-(d * z.im)) / 2) := by
    calc
      (c / 2) * Real.exp (-(d * z.im)) =
          (c * (1 / 2)) * Real.exp (-(d * z.im)) := by
        exact congrArg
          (fun y : ℝ => y * Real.exp (-(d * z.im)))
          (div_eq_mul_one_div c 2)
      _ = c * ((1 / 2) * Real.exp (-(d * z.im))) := by
        exact mul_assoc c (1 / 2) (Real.exp (-(d * z.im)))
      _ = c * (Real.exp (-(d * z.im)) * (1 / 2)) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (mul_comm (1 / 2) (Real.exp (-(d * z.im))))
      _ = c * (Real.exp (-(d * z.im)) / 2) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (div_eq_mul_one_div (Real.exp (-(d * z.im))) 2).symm
  calc
    (c / 2) * Real.exp (-(d * z.im)) ≤
        c * Real.cosh (d * z.im) := by
      calc
        (c / 2) * Real.exp (-(d * z.im)) =
            c * (Real.exp (-(d * z.im)) / 2) := hleft_eq
        _ ≤ c * Real.cosh (d * z.im) := hmul_lower
    _ = (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
      (verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_eq
        a b d hz).symm

/-- On the left boundary ray, the subcritical barrier real part has
exponential lower growth in the lower-tail height. -/
theorem verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_exp_neg
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    {z : ℂ}
    (hz : z.re = a) :
    (Real.cos (d * (-((b - a) / 2))) / 2) * Real.exp (-(d * z.im)) ≤
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re := by
  let c : ℝ := Real.cos (d * (-((b - a) / 2)))
  have hc_pos : 0 < c :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_cos_pos
      hab hd_pos hd_threshold
  have hc_nonneg : 0 ≤ c :=
    le_of_lt hc_pos
  have hcosh_lower :
      Real.exp (-(d * z.im)) / 2 ≤ Real.cosh (d * z.im) :=
    real_exp_neg_half_le_cosh (d * z.im)
  have hmul_lower :
      c * (Real.exp (-(d * z.im)) / 2) ≤ c * Real.cosh (d * z.im) :=
    mul_le_mul_of_nonneg_left hcosh_lower hc_nonneg
  have hleft_eq :
      (c / 2) * Real.exp (-(d * z.im)) =
        c * (Real.exp (-(d * z.im)) / 2) := by
    calc
      (c / 2) * Real.exp (-(d * z.im)) =
          (c * (1 / 2)) * Real.exp (-(d * z.im)) := by
        exact congrArg
          (fun y : ℝ => y * Real.exp (-(d * z.im)))
          (div_eq_mul_one_div c 2)
      _ = c * ((1 / 2) * Real.exp (-(d * z.im))) := by
        exact mul_assoc c (1 / 2) (Real.exp (-(d * z.im)))
      _ = c * (Real.exp (-(d * z.im)) * (1 / 2)) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (mul_comm (1 / 2) (Real.exp (-(d * z.im))))
      _ = c * (Real.exp (-(d * z.im)) / 2) := by
        exact congrArg
          (fun y : ℝ => c * y)
          (div_eq_mul_one_div (Real.exp (-(d * z.im))) 2).symm
  calc
    (c / 2) * Real.exp (-(d * z.im)) ≤
        c * Real.cosh (d * z.im) := by
      calc
        (c / 2) * Real.exp (-(d * z.im)) =
            c * (Real.exp (-(d * z.im)) / 2) := hleft_eq
        _ ≤ c * Real.cosh (d * z.im) := hmul_lower
    _ = (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
      (verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_eq
        a b d hz).symm

/-- Right-boundary pointwise estimate for the subcritical damped family,
before the scalar absorption step. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_preAbsorption
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hboundary :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    {z : ℂ}
    (hz_re : z.re = b)
    (hz_im : 1 ≤ z.im) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε *
            ((Real.cos (d * ((b - a) / 2)) / 2) *
              Real.exp (d * z.im)))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hnorm_eq :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hL :
      (Real.cos (d * ((b - a) / 2)) / 2) * Real.exp (d * z.im) ≤
        (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_exp
      hab hd_pos hd_threshold hz_re
  have hg :
      ‖g‖ ≤
        Real.exp
          (-(ε *
            ((Real.cos (d * ((b - a) / 2)) / 2) *
              Real.exp (d * z.im)))) :=
    verticalStripSubcriticalCosineDampingFactor_norm_le_exp_neg_of_re_lower
      hε hL
  have hf :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
    hboundary z hz_re hz_im
  have hf_rhs_nonneg :
      0 ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
    le_trans (norm_nonneg (f z)) hf
  have hg_nonneg :
      0 ≤
        Real.exp
          (-(ε *
            ((Real.cos (d * ((b - a) / 2)) / 2) *
              Real.exp (d * z.im)))) :=
    le_of_lt
      (Real.exp_pos
        (-(ε *
          ((Real.cos (d * ((b - a) / 2)) / 2) *
            Real.exp (d * z.im)))))
  have hmul :
      ‖f z‖ * ‖g‖ ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
          Real.exp
            (-(ε *
              ((Real.cos (d * ((b - a) / 2)) / 2) *
                Real.exp (d * z.im)))) :=
    mul_le_mul hf hg (norm_nonneg g) hf_rhs_nonneg
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤
          (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
            Real.exp
              (-(ε *
                ((Real.cos (d * ((b - a) / 2)) / 2) *
                  Real.exp (d * z.im)))))
      hnorm_eq.symm
      hmul

/-- Left-boundary pointwise estimate for the subcritical damped family,
before the scalar absorption step. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_preAbsorption
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hboundary :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    {z : ℂ}
    (hz_re : z.re = a)
    (hz_im : 1 ≤ z.im) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε *
            ((Real.cos (d * (-((b - a) / 2))) / 2) *
              Real.exp (d * z.im)))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hnorm_eq :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hL :
      (Real.cos (d * (-((b - a) / 2))) / 2) * Real.exp (d * z.im) ≤
        (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_exp
      hab hd_pos hd_threshold hz_re
  have hg :
      ‖g‖ ≤
        Real.exp
          (-(ε *
            ((Real.cos (d * (-((b - a) / 2))) / 2) *
              Real.exp (d * z.im)))) :=
    verticalStripSubcriticalCosineDampingFactor_norm_le_exp_neg_of_re_lower
      hε hL
  have hf :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
    hboundary z hz_re hz_im
  have hf_rhs_nonneg :
      0 ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
    le_trans (norm_nonneg (f z)) hf
  have hg_nonneg :
      0 ≤
        Real.exp
          (-(ε *
            ((Real.cos (d * (-((b - a) / 2))) / 2) *
              Real.exp (d * z.im)))) :=
    le_of_lt
      (Real.exp_pos
        (-(ε *
          ((Real.cos (d * (-((b - a) / 2))) / 2) *
            Real.exp (d * z.im)))))
  have hmul :
      ‖f z‖ * ‖g‖ ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
          Real.exp
            (-(ε *
              ((Real.cos (d * (-((b - a) / 2))) / 2) *
                Real.exp (d * z.im)))) :=
    mul_le_mul hf hg (norm_nonneg g) hf_rhs_nonneg
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤
          (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
            Real.exp
              (-(ε *
                ((Real.cos (d * (-((b - a) / 2))) / 2) *
                  Real.exp (d * z.im)))))
      hnorm_eq.symm
      hmul

/-- A fixed half-rate exponential is eventually dominated by any positive
multiple of the full-rate exponential. -/
theorem real_const_mul_exp_half_rate_eventually_le_pos_mul_exp_rate
    (D E d : ℝ)
    (hE : 0 < E)
    (hd : 0 < d) :
    ∀ᶠ T : ℝ in Filter.atTop,
      D * Real.exp ((d / 2) * T) ≤ E * Real.exp (d * T) := by
  have hhalf_pos : 0 < d / 2 :=
    div_pos hd zero_lt_two
  have htendsto :
      Filter.Tendsto (fun T : ℝ => Real.exp ((d / 2) * T))
        Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop hhalf_pos Filter.tendsto_id)
  have heventual :
      ∀ᶠ T : ℝ in Filter.atTop,
        D / E ≤ Real.exp ((d / 2) * T) :=
    (Filter.tendsto_atTop.mp htendsto) (D / E)
  exact
    heventual.mono
      (fun T hT =>
        by
          have hE_nonneg : 0 ≤ E :=
            le_of_lt hE
          have hmul_left : D ≤ E * Real.exp ((d / 2) * T) := by
            have hmul :
                E * (D / E) ≤ E * Real.exp ((d / 2) * T) :=
              mul_le_mul_of_nonneg_left hT hE_nonneg
            have hcancel : E * (D / E) = D := by
              calc
                E * (D / E) = E * (D * E⁻¹) := by
                  exact congrArg (fun x : ℝ => E * x) (div_eq_mul_inv D E)
                _ = (E * E⁻¹) * D := by
                  calc
                    E * (D * E⁻¹) = E * (E⁻¹ * D) := by
                      exact congrArg (fun x : ℝ => E * x) (mul_comm D E⁻¹)
                    _ = (E * E⁻¹) * D := by
                      exact (mul_assoc E E⁻¹ D).symm
                _ = 1 * D := by
                  exact congrArg (fun x : ℝ => x * D)
                    (mul_inv_cancel₀ (ne_of_gt hE))
                _ = D := one_mul D
            exact
              Eq.subst
                (motive := fun x : ℝ => x ≤ E * Real.exp ((d / 2) * T))
                hcancel
                hmul
          have hexp_split :
              Real.exp (d * T) =
                Real.exp ((d / 2) * T) * Real.exp ((d / 2) * T) := by
            have harg :
                d * T = (d / 2) * T + (d / 2) * T := by
              calc
                d * T = ((d / 2) + (d / 2)) * T := by
                  have hsum : d / 2 + d / 2 = d := by
                    calc
                      d / 2 + d / 2 = (d + d) / 2 := by
                        exact (add_div d d 2).symm
                      _ = (2 * d) / 2 := by
                        exact congrArg (fun x : ℝ => x / 2) (two_mul d).symm
                      _ = d := by
                        exact mul_div_cancel_left₀ d
                          (show (2 : ℝ) ≠ 0 from two_ne_zero)
                  exact congrArg (fun x : ℝ => x * T) hsum.symm
                _ = (d / 2) * T + (d / 2) * T := by
                  exact add_mul (d / 2) (d / 2) T
            calc
              Real.exp (d * T) =
                  Real.exp (((d / 2) * T) + ((d / 2) * T)) := by
                exact congrArg Real.exp harg
              _ =
                  Real.exp ((d / 2) * T) *
                    Real.exp ((d / 2) * T) :=
                Real.exp_add ((d / 2) * T) ((d / 2) * T)
          have hexp_nonneg :
              0 ≤ Real.exp ((d / 2) * T) :=
            le_of_lt (Real.exp_pos ((d / 2) * T))
          have hmul :
              D * Real.exp ((d / 2) * T) ≤
                (E * Real.exp ((d / 2) * T)) *
                  Real.exp ((d / 2) * T) :=
            mul_le_mul_of_nonneg_right hmul_left hexp_nonneg
          have hright :
              (E * Real.exp ((d / 2) * T)) *
                  Real.exp ((d / 2) * T) =
                E * Real.exp (d * T) := by
            calc
              (E * Real.exp ((d / 2) * T)) *
                  Real.exp ((d / 2) * T) =
                E *
                  (Real.exp ((d / 2) * T) *
                    Real.exp ((d / 2) * T)) := by
                  exact mul_assoc E
                    (Real.exp ((d / 2) * T))
                    (Real.exp ((d / 2) * T))
              _ = E * Real.exp (d * T) := by
                exact congrArg (fun x : ℝ => E * x) hexp_split.symm
          exact
            Eq.subst
              (motive := fun x : ℝ =>
                D * Real.exp ((d / 2) * T) ≤ x)
              hright
              hmul)

/-- The scalar finite-order boundary envelope times the subcritical absorber is
eventually bounded on the upper tail. -/
theorem finiteOrder_exp_mul_subcritical_absorber_eventually_le_one
    (A B K d ε : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hK : 0 < K)
    (hd : 0 < d)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
      A * Real.exp (B * (1 + T) ^ m) *
          Real.exp (-(ε * (K * Real.exp (d * T)))) ≤ 1 := by
  have hhalf_pos : 0 < d / 2 :=
    div_pos hd zero_lt_two
  match
    gammaBoundaryPL_finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
      A B (d / 2) m hA hB hhalf_pos
  with
  | ⟨D, hD_pos, hfinite_exp⟩ =>
      let E : ℝ := ε * K / 2
      have hE_pos : 0 < E :=
        div_pos (mul_pos hε hK) zero_lt_two
      have hcompare :
          ∀ᶠ T : ℝ in Filter.atTop,
            D * Real.exp ((d / 2) * T) ≤ E * Real.exp (d * T) :=
        real_const_mul_exp_half_rate_eventually_le_pos_mul_exp_rate
          D E d hE_pos hd
      have hboth :
          ∀ᶠ T : ℝ in Filter.atTop,
            (Real.log A + B * (1 + T) ^ m ≤ D * Real.exp ((d / 2) * T)) ∧
              D * Real.exp ((d / 2) * T) ≤ E * Real.exp (d * T) :=
        hfinite_exp.and hcompare
      exact
        hboth.mono
          (fun T hT =>
            by
              have htotal :
                  Real.log A + B * (1 + T) ^ m ≤
                    E * Real.exp (d * T) :=
                le_trans hT.1 hT.2
              have hE_eq :
                  E * Real.exp (d * T) =
                    (ε * (K * Real.exp (d * T))) / 2 := by
                calc
                  E * Real.exp (d * T) =
                      (ε * K / 2) * Real.exp (d * T) := rfl
                  _ =
                      ((ε * K) * (1 / 2)) * Real.exp (d * T) := by
                    exact congrArg
                      (fun x : ℝ => x * Real.exp (d * T))
                      (div_eq_mul_one_div (ε * K) 2)
                  _ =
                      (ε * K) * ((1 / 2) * Real.exp (d * T)) := by
                    exact mul_assoc (ε * K) (1 / 2) (Real.exp (d * T))
                  _ =
                      (ε * K) * (Real.exp (d * T) * (1 / 2)) := by
                    exact congrArg
                      (fun x : ℝ => (ε * K) * x)
                      (mul_comm (1 / 2) (Real.exp (d * T)))
                  _ =
                      ((ε * K) * Real.exp (d * T)) * (1 / 2) := by
                    exact (mul_assoc (ε * K) (Real.exp (d * T)) (1 / 2)).symm
                  _ =
                      (ε * (K * Real.exp (d * T))) * (1 / 2) := by
                    exact congrArg
                      (fun x : ℝ => x * (1 / 2))
                      (mul_assoc ε K (Real.exp (d * T)))
                  _ =
                      (ε * (K * Real.exp (d * T))) / 2 := by
                    exact (div_eq_mul_one_div
                      (ε * (K * Real.exp (d * T))) 2).symm
              have hhalf :
                  Real.log A + B * (1 + T) ^ m ≤
                    (ε * (K * Real.exp (d * T))) / 2 :=
                Eq.subst
                  (motive := fun x : ℝ =>
                    Real.log A + B * (1 + T) ^ m ≤ x)
                  hE_eq
                  htotal
              have habs_pos :
                  0 < ε * (K * Real.exp (d * T)) :=
                mul_pos hε (mul_pos hK (Real.exp_pos (d * T)))
              have hhalf_le_full :
                  (ε * (K * Real.exp (d * T))) / 2 ≤
                    ε * (K * Real.exp (d * T)) := by
                have hnonneg :
                    0 ≤ ε * (K * Real.exp (d * T)) :=
                  le_of_lt habs_pos
                have hhalf_eq :
                    (ε * (K * Real.exp (d * T))) / 2 =
                      (1 / 2 : ℝ) * (ε * (K * Real.exp (d * T))) := by
                  calc
                    (ε * (K * Real.exp (d * T))) / 2 =
                        (ε * (K * Real.exp (d * T))) * (1 / 2 : ℝ) := by
                      exact div_eq_mul_one_div
                        (ε * (K * Real.exp (d * T))) 2
                    _ = (1 / 2 : ℝ) * (ε * (K * Real.exp (d * T))) :=
                      mul_comm (ε * (K * Real.exp (d * T))) (1 / 2 : ℝ)
                have hone_half_le_one : (1 / 2 : ℝ) ≤ 1 :=
                  (div_le_one zero_lt_two).mpr one_le_two
                have hscaled :
                    (1 / 2 : ℝ) *
                        (ε * (K * Real.exp (d * T))) ≤
                      1 * (ε * (K * Real.exp (d * T))) :=
                  mul_le_mul_of_nonneg_right hone_half_le_one hnonneg
                exact
                  Eq.subst
                    (motive := fun x : ℝ =>
                      x ≤ ε * (K * Real.exp (d * T)))
                    hhalf_eq.symm
                    (Eq.subst
                      (motive := fun x : ℝ =>
                        (1 / 2 : ℝ) *
                            (ε * (K * Real.exp (d * T))) ≤ x)
                      (one_mul (ε * (K * Real.exp (d * T))))
                      hscaled)
              have hsum_nonpos :
                  Real.log A + B * (1 + T) ^ m -
                      ε * (K * Real.exp (d * T)) ≤ 0 := by
                have hle_full :
                    Real.log A + B * (1 + T) ^ m ≤
                      ε * (K * Real.exp (d * T)) :=
                  le_trans hhalf hhalf_le_full
                exact sub_nonpos.mpr hle_full
              have hleft_exp :
                  A * Real.exp (B * (1 + T) ^ m) *
                      Real.exp (-(ε * (K * Real.exp (d * T)))) =
                    Real.exp
                      (Real.log A + B * (1 + T) ^ m -
                        ε * (K * Real.exp (d * T))) := by
                calc
                  A * Real.exp (B * (1 + T) ^ m) *
                      Real.exp (-(ε * (K * Real.exp (d * T)))) =
                    Real.exp (Real.log A) *
                        Real.exp (B * (1 + T) ^ m) *
                        Real.exp (-(ε * (K * Real.exp (d * T)))) := by
                      exact congrArg
                        (fun x : ℝ =>
                          x * Real.exp (B * (1 + T) ^ m) *
                            Real.exp (-(ε * (K * Real.exp (d * T)))))
                        (Real.exp_log hA).symm
                  _ =
                    Real.exp (Real.log A + B * (1 + T) ^ m) *
                        Real.exp (-(ε * (K * Real.exp (d * T)))) := by
                      exact congrArg
                        (fun x : ℝ =>
                          x * Real.exp (-(ε * (K * Real.exp (d * T)))))
                        (Real.exp_add (Real.log A) (B * (1 + T) ^ m)).symm
                  _ =
                    Real.exp
                      ((Real.log A + B * (1 + T) ^ m) +
                        (-(ε * (K * Real.exp (d * T))))) := by
                      exact
                        (Real.exp_add
                          (Real.log A + B * (1 + T) ^ m)
                          (-(ε * (K * Real.exp (d * T))))).symm
                  _ =
                    Real.exp
                      (Real.log A + B * (1 + T) ^ m -
                        ε * (K * Real.exp (d * T))) := by
                      exact congrArg Real.exp
                        (sub_eq_add_neg
                          (Real.log A + B * (1 + T) ^ m)
                          (ε * (K * Real.exp (d * T)))).symm
              have hexp_le_one :
                  Real.exp
                      (Real.log A + B * (1 + T) ^ m -
                        ε * (K * Real.exp (d * T))) ≤ 1 :=
                Real.exp_le_one_iff.mpr hsum_nonpos
              exact
                Eq.subst
                  (motive := fun x : ℝ => x ≤ 1)
                  hleft_exp.symm
                  hexp_le_one)

/-- The finite-order boundary envelope is eventually absorbed by a shifted
upper-tail double-exponential damping term. -/
theorem finiteOrder_exp_mul_shifted_upperTail_absorber_eventually_le_one
    (A B K s M ε : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hK : 0 < K)
    (hs : 0 < s)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop,
      A * Real.exp (B * (1 + T) ^ m) *
          Real.exp (-(ε * (K * Real.exp (s * (M + T))))) ≤ 1 := by
  let K' : ℝ := K * Real.exp (s * M)
  have hK'_pos : 0 < K' :=
    mul_pos hK (Real.exp_pos (s * M))
  have htail :
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(ε * (K' * Real.exp (s * T)))) ≤ 1 :=
    finiteOrder_exp_mul_subcritical_absorber_eventually_le_one
      A B K' s ε m hA hB hK'_pos hs hε
  exact
    htail.mono
      fun T hT =>
        have hshift_exp :
            Real.exp (s * (M + T)) =
              Real.exp (s * M) * Real.exp (s * T) := by
          have hmul_add :
              s * (M + T) = s * M + s * T :=
            mul_add s M T
          calc
            Real.exp (s * (M + T)) =
                Real.exp (s * M + s * T) := by
              exact congrArg Real.exp hmul_add
            _ = Real.exp (s * M) * Real.exp (s * T) :=
              Real.exp_add (s * M) (s * T)
        have hkernel :
            K * Real.exp (s * (M + T)) =
              K' * Real.exp (s * T) := by
          calc
            K * Real.exp (s * (M + T)) =
                K * (Real.exp (s * M) * Real.exp (s * T)) := by
              exact congrArg (fun x : ℝ => K * x) hshift_exp
            _ = (K * Real.exp (s * M)) * Real.exp (s * T) := by
              exact (mul_assoc K (Real.exp (s * M)) (Real.exp (s * T))).symm
            _ = K' * Real.exp (s * T) := rfl
        have harg :
            ε * (K * Real.exp (s * (M + T))) =
              ε * (K' * Real.exp (s * T)) :=
          congrArg (fun x : ℝ => ε * x) hkernel
        have hfactor :
            Real.exp (-(ε * (K * Real.exp (s * (M + T))))) =
              Real.exp (-(ε * (K' * Real.exp (s * T)))) :=
          congrArg Real.exp (congrArg Neg.neg harg)
        have htotal :
            A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(ε * (K * Real.exp (s * (M + T))))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(ε * (K' * Real.exp (s * T)))) :=
          congrArg
            (fun x : ℝ => A * Real.exp (B * (1 + T) ^ m) * x)
            hfactor
        Eq.subst
          (motive := fun x : ℝ => x ≤ 1)
          htotal.symm
          hT

/-- Right-boundary scalar absorption supplied by the subcritical cosine
barrier exponent. -/
theorem verticalStripSubcriticalCosineDampingExponent_rightBoundary_re_le_neg_eps_cos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re ≤
      -ε * Real.cos (d * ((b - a) / 2)) := by
  have hre_ge :
      Real.cos (d * ((b - a) / 2)) ≤
        (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_cos
      hab hd_pos hd_threshold hz
  have hmul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re ≤
        -ε * Real.cos (d * ((b - a) / 2)) :=
    mul_le_mul_of_nonpos_left hre_ge (neg_nonpos.mpr hε)
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul
      a b d ε z
  exact le_trans (le_of_eq hre) hmul

/-- Left-boundary scalar absorption supplied by the subcritical cosine
barrier exponent. -/
theorem verticalStripSubcriticalCosineDampingExponent_leftBoundary_re_le_neg_eps_cos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re ≤
      -ε * Real.cos (d * (-((b - a) / 2))) := by
  have hre_ge :
      Real.cos (d * (-((b - a) / 2))) ≤
        (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_cos
      hab hd_pos hd_threshold hz
  have hmul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re ≤
        -ε * Real.cos (d * (-((b - a) / 2))) :=
    mul_le_mul_of_nonpos_left hre_ge (neg_nonpos.mpr hε)
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul
      a b d ε z
  exact le_trans (le_of_eq hre) hmul

/-- Exact right-boundary real-part formula for the subcritical damping
exponent, retaining the growing `cosh` factor. -/
theorem verticalStripSubcriticalCosineDampingExponent_rightBoundary_re_eq
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      -ε *
        (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im)) := by
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul
      a b d ε z
  have hboundary :
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im) :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_eq
      a b d hz
  exact Eq.trans hre
    (congrArg (fun x : ℝ => -ε * x) hboundary)

/-- Exact left-boundary real-part formula for the subcritical damping
exponent, retaining the growing `cosh` factor. -/
theorem verticalStripSubcriticalCosineDampingExponent_leftBoundary_re_eq
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = a) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re =
      -ε *
        (Real.cos (d * (-((b - a) / 2))) * Real.cosh (d * z.im)) := by
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul
      a b d ε z
  have hboundary :
      (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        Real.cos (d * (-((b - a) / 2))) * Real.cosh (d * z.im) :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_eq
      a b d hz
  exact Eq.trans hre
    (congrArg (fun x : ℝ => -ε * x) hboundary)

/-- Exact right-boundary norm formula for the subcritical cosine damping
factor, retaining the growing `cosh` factor. -/
theorem verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_eq
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ =
      Real.exp
        (-ε *
          (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))) := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have hre :
      w.re =
        -ε *
          (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im)) :=
    verticalStripSubcriticalCosineDampingExponent_rightBoundary_re_eq
      a b d ε hz
  exact Eq.trans hnorm (congrArg Real.exp hre)

/-- Exact left-boundary norm formula for the subcritical cosine damping
factor, retaining the growing `cosh` factor. -/
theorem verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_eq
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = a) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ =
      Real.exp
        (-ε *
          (Real.cos (d * (-((b - a) / 2))) *
            Real.cosh (d * z.im))) := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have hre :
      w.re =
        -ε *
          (Real.cos (d * (-((b - a) / 2))) *
            Real.cosh (d * z.im)) :=
    verticalStripSubcriticalCosineDampingExponent_leftBoundary_re_eq
      a b d ε hz
  exact Eq.trans hnorm (congrArg Real.exp hre)

/-- Exact right-boundary norm formula for the subcritical cosine-damped
family. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_eq
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = b) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
      ‖f z‖ *
        Real.exp
          (-ε *
            (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hfamily :
      verticalStripSubcriticalCosineDampedFamily f a b d ε z = f z * g := by
    rfl
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    exact Eq.trans (congrArg norm hfamily) (norm_mul (f z) g)
  have hg :
      ‖g‖ =
        Real.exp
          (-ε *
            (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))) :=
    verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_eq
      a b d ε hz
  exact Eq.trans hnorm_mul
    (congrArg (fun x : ℝ => ‖f z‖ * x) hg)

/-- Exact left-boundary norm formula for the subcritical cosine-damped
family. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_eq
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    {z : ℂ}
    (hz : z.re = a) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
      ‖f z‖ *
        Real.exp
          (-ε *
            (Real.cos (d * (-((b - a) / 2))) *
              Real.cosh (d * z.im))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hfamily :
      verticalStripSubcriticalCosineDampedFamily f a b d ε z = f z * g := by
    rfl
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    exact Eq.trans (congrArg norm hfamily) (norm_mul (f z) g)
  have hg :
      ‖g‖ =
        Real.exp
          (-ε *
            (Real.cos (d * (-((b - a) / 2))) *
              Real.cosh (d * z.im))) :=
    verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_eq
      a b d ε hz
  exact Eq.trans hnorm_mul
    (congrArg (fun x : ℝ => ‖f z‖ * x) hg)

/-- Right-boundary finite-order envelope transported through the exact
subcritical damping factor. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_le_envelope_mul_absorber
    (f : ℂ → ℂ)
    (a b d ε A B : ℝ)
    (m : ℕ)
    {z : ℂ}
    (hz : z.re = b)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-ε *
            (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))) := by
  let absorber : ℝ :=
    Real.exp
      (-ε *
        (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im)))
  have habs_nonneg : 0 ≤ absorber :=
    le_of_lt (Real.exp_pos
      (-ε *
        (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))))
  have hmul :
      ‖f z‖ * absorber ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * absorber :=
    mul_le_mul_of_nonneg_right hboundary habs_nonneg
  have hnorm :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * absorber :=
    verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_eq
      f a b d ε hz
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
          Real.exp
            (-ε *
              (Real.cos (d * ((b - a) / 2)) * Real.cosh (d * z.im))))
    hnorm.symm
    hmul

/-- Left-boundary finite-order envelope transported through the exact
subcritical damping factor. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_le_envelope_mul_absorber
    (f : ℂ → ℂ)
    (a b d ε A B : ℝ)
    (m : ℕ)
    {z : ℂ}
    (hz : z.re = a)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-ε *
            (Real.cos (d * (-((b - a) / 2))) *
              Real.cosh (d * z.im))) := by
  let absorber : ℝ :=
    Real.exp
      (-ε *
        (Real.cos (d * (-((b - a) / 2))) * Real.cosh (d * z.im)))
  have habs_nonneg : 0 ≤ absorber :=
    le_of_lt (Real.exp_pos
      (-ε *
        (Real.cos (d * (-((b - a) / 2))) * Real.cosh (d * z.im))))
  have hmul :
      ‖f z‖ * absorber ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) * absorber :=
    mul_le_mul_of_nonneg_right hboundary habs_nonneg
  have hnorm :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * absorber :=
    verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_eq
      f a b d ε hz
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
          Real.exp
            (-ε *
              (Real.cos (d * (-((b - a) / 2))) *
                Real.cosh (d * z.im))))
    hnorm.symm
    hmul

/-- Right-boundary norm absorption for the subcritical cosine damping factor. -/
theorem verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_le_exp_neg_eps_cos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp (-ε * Real.cos (d * ((b - a) / 2))) := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hre :
      w.re ≤ -ε * Real.cos (d * ((b - a) / 2)) :=
    verticalStripSubcriticalCosineDampingExponent_rightBoundary_re_le_neg_eps_cos
      hab hd_pos hd_threshold hε hz
  have hexp :
      Real.exp w.re ≤
        Real.exp (-ε * Real.cos (d * ((b - a) / 2))) :=
    Real.exp_le_exp.mpr hre
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ Real.exp (-ε * Real.cos (d * ((b - a) / 2))))
    hnorm.symm
    hexp

/-- Left-boundary norm absorption for the subcritical cosine damping factor. -/
theorem verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_le_exp_neg_eps_cos
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp (-ε * Real.cos (d * (-((b - a) / 2)))) := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hre :
      w.re ≤ -ε * Real.cos (d * (-((b - a) / 2))) :=
    verticalStripSubcriticalCosineDampingExponent_leftBoundary_re_le_neg_eps_cos
      hab hd_pos hd_threshold hε hz
  have hexp :
      Real.exp w.re ≤
        Real.exp (-ε * Real.cos (d * (-((b - a) / 2)))) :=
    Real.exp_le_exp.mpr hre
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ Real.exp (-ε * Real.cos (d * (-((b - a) / 2)))))
    hnorm.symm
    hexp

/-- Right-boundary subcritical damping has superexponential upper-tail decay. -/
theorem verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_le_exp_neg_exp
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp
        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
          Real.exp (d * z.im))) := by
  let K : ℝ :=
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re
  let c : ℝ := Real.cos (d * ((b - a) / 2))
  let L : ℝ := (c / 2) * Real.exp (d * z.im)
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hL_le_K : L ≤ K :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_exp
      hab hd_pos hd_threshold hz
  have hmul_le : ε * L ≤ ε * K :=
    mul_le_mul_of_nonneg_left hL_le_K hε
  have hneg_le : -(ε * K) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have hre :
      w.re = -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hneg_mul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -(ε * K) :=
    neg_mul ε K
  have hre_le :
      w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ -(ε * L))
      (Eq.trans hre hneg_mul).symm
      hneg_le
  have hexp_le :
      Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have harg :
      -(ε * L) =
        -(ε * (c / 2) * Real.exp (d * z.im)) := by
    exact congrArg Neg.neg
      (mul_assoc ε (c / 2) (Real.exp (d * z.im))).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ y)
      (congrArg Real.exp harg)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ Real.exp (-(ε * L)))
        hnorm.symm
        hexp_le)

/-- Left-boundary subcritical damping has superexponential upper-tail decay. -/
theorem verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_le_exp_neg_exp
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp
        (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
          Real.exp (d * z.im))) := by
  let K : ℝ :=
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re
  let c : ℝ := Real.cos (d * (-((b - a) / 2)))
  let L : ℝ := (c / 2) * Real.exp (d * z.im)
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hL_le_K : L ≤ K :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_exp
      hab hd_pos hd_threshold hz
  have hmul_le : ε * L ≤ ε * K :=
    mul_le_mul_of_nonneg_left hL_le_K hε
  have hneg_le : -(ε * K) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have hre :
      w.re = -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hneg_mul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -(ε * K) :=
    neg_mul ε K
  have hre_le :
      w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ -(ε * L))
      (Eq.trans hre hneg_mul).symm
      hneg_le
  have hexp_le :
      Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have harg :
      -(ε * L) =
        -(ε * (c / 2) * Real.exp (d * z.im)) := by
    exact congrArg Neg.neg
      (mul_assoc ε (c / 2) (Real.exp (d * z.im))).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ y)
      (congrArg Real.exp harg)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ Real.exp (-(ε * L)))
        hnorm.symm
        hexp_le)

/-- Right-boundary subcritical damping has superexponential lower-tail decay. -/
theorem verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_le_exp_neg_exp_neg
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp
        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
          Real.exp (-(d * z.im)))) := by
  let K : ℝ :=
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re
  let c : ℝ := Real.cos (d * ((b - a) / 2))
  let L : ℝ := (c / 2) * Real.exp (-(d * z.im))
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hL_le_K : L ≤ K :=
    verticalStripSubcriticalCosineBarrierKernel_rightBoundary_re_ge_exp_neg
      hab hd_pos hd_threshold hz
  have hmul_le : ε * L ≤ ε * K :=
    mul_le_mul_of_nonneg_left hL_le_K hε
  have hneg_le : -(ε * K) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have hre :
      w.re = -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hneg_mul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -(ε * K) :=
    neg_mul ε K
  have hre_le :
      w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ -(ε * L))
      (Eq.trans hre hneg_mul).symm
      hneg_le
  have hexp_le :
      Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have harg :
      -(ε * L) =
        -(ε * (c / 2) * Real.exp (-(d * z.im))) := by
    exact congrArg Neg.neg
      (mul_assoc ε (c / 2) (Real.exp (-(d * z.im)))).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ y)
      (congrArg Real.exp harg)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ Real.exp (-(ε * L)))
        hnorm.symm
        hexp_le)

/-- Left-boundary subcritical damping has superexponential lower-tail decay. -/
theorem verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_le_exp_neg_exp_neg
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤
      Real.exp
        (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
          Real.exp (-(d * z.im)))) := by
  let K : ℝ :=
    (verticalStripSubcriticalCosineBarrierKernel a b d z).re
  let c : ℝ := Real.cos (d * (-((b - a) / 2)))
  let L : ℝ := (c / 2) * Real.exp (-(d * z.im))
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hL_le_K : L ≤ K :=
    verticalStripSubcriticalCosineBarrierKernel_leftBoundary_re_ge_exp_neg
      hab hd_pos hd_threshold hz
  have hmul_le : ε * L ≤ ε * K :=
    mul_le_mul_of_nonneg_left hL_le_K hε
  have hneg_le : -(ε * K) ≤ -(ε * L) :=
    neg_le_neg hmul_le
  have hre :
      w.re = -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hneg_mul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -(ε * K) :=
    neg_mul ε K
  have hre_le :
      w.re ≤ -(ε * L) :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ -(ε * L))
      (Eq.trans hre hneg_mul).symm
      hneg_le
  have hexp_le :
      Real.exp w.re ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr hre_le
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  have harg :
      -(ε * L) =
        -(ε * (c / 2) * Real.exp (-(d * z.im))) := by
    exact congrArg Neg.neg
      (mul_assoc ε (c / 2) (Real.exp (-(d * z.im)))).symm
  exact
    Eq.subst
      (motive := fun y : ℝ =>
        ‖Complex.exp
            (-((ε : ℝ) : ℂ) *
              verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ y)
      (congrArg Real.exp harg)
      (Eq.subst
        (motive := fun y : ℝ => y ≤ Real.exp (-(ε * L)))
        hnorm.symm
        hexp_le)

/-- Right-boundary finite-order envelope transported through the
superexponential upper-tail damping estimate. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_le_envelope_mul_exp_absorber
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
            Real.exp (d * z.im))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  let envelope : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
  let absorber : ℝ :=
    Real.exp
      (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
        Real.exp (d * z.im)))
  have hfactor : ‖g‖ ≤ absorber :=
    verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_le_exp_neg_exp
      hab hd_pos hd_threshold hε hz
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hfactor_nonneg : 0 ≤ ‖g‖ :=
    norm_nonneg g
  have hfirst :
      ‖f z‖ * ‖g‖ ≤ envelope * ‖g‖ :=
    mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
  have hsecond :
      envelope * ‖g‖ ≤ envelope * absorber :=
    mul_le_mul_of_nonneg_left hfactor
      (le_trans (norm_nonneg (f z)) hboundary)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ envelope * absorber)
      hnorm_mul.symm
      (le_trans hfirst hsecond)

/-- Left-boundary finite-order envelope transported through the
superexponential upper-tail damping estimate. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_le_envelope_mul_exp_absorber
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
            Real.exp (d * z.im))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  let envelope : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
  let absorber : ℝ :=
    Real.exp
      (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
        Real.exp (d * z.im)))
  have hfactor : ‖g‖ ≤ absorber :=
    verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_le_exp_neg_exp
      hab hd_pos hd_threshold hε hz
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hfactor_nonneg : 0 ≤ ‖g‖ :=
    norm_nonneg g
  have hfirst :
      ‖f z‖ * ‖g‖ ≤ envelope * ‖g‖ :=
    mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
  have hsecond :
      envelope * ‖g‖ ≤ envelope * absorber :=
    mul_le_mul_of_nonneg_left hfactor
      (le_trans (norm_nonneg (f z)) hboundary)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ envelope * absorber)
      hnorm_mul.symm
      (le_trans hfirst hsecond)

/-- A fixed polynomial exponent is eventually absorbed by any positive
exponential scale on the upper real tail. -/
theorem finiteOrderPolynomialExponent_eventually_le_exp_absorber_half
    {B K d : ℝ}
    {m : ℕ}
    (hB : 0 < B)
    (hK : 0 < K)
    (hd : 0 < d) :
    ∀ᶠ y in Filter.atTop,
      B * (1 + y) ^ m ≤ (K / 2) * Real.exp (d * y) := by
  let c : ℝ := K / (2 * B * Real.exp d)
  have hc_pos : 0 < c :=
    div_pos hK
      (mul_pos (mul_pos zero_lt_two hB) (Real.exp_pos d))
  have hshift : Filter.Tendsto (fun y : ℝ => 1 + y) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2
      (fun R =>
        Filter.eventually_atTop.2
          ⟨R, fun y hy =>
            calc
              R ≤ y := hy
              _ ≤ 1 + y := le_add_of_nonneg_left zero_le_one⟩)
  have hlittle :
      (fun y : ℝ => (1 + y) ^ m) =o[Filter.atTop]
        fun y : ℝ => Real.exp (d * (1 + y)) :=
    (isLittleO_pow_exp_pos_mul_atTop m hd).comp_tendsto hshift
  have hraw :
      ∀ᶠ y in Filter.atTop,
        ‖(1 + y) ^ m‖ ≤ c * ‖Real.exp (d * (1 + y))‖ :=
    hlittle.bound hc_pos
  have hnonneg :
      ∀ᶠ y : ℝ in Filter.atTop, 0 ≤ (1 + y) ^ m :=
    (eventually_ge_atTop (0 : ℝ)).mono
      fun y hy =>
        pow_nonneg (add_nonneg zero_le_one hy) m
  exact
    (hraw.and hnonneg).mono
      fun y hy =>
        have hpow_abs :
            ‖(1 + y) ^ m‖ = (1 + y) ^ m :=
          Real.norm_of_nonneg hy.2
        have hexp_abs :
            ‖Real.exp (d * (1 + y))‖ = Real.exp (d * (1 + y)) :=
          Real.norm_of_nonneg (le_of_lt (Real.exp_pos (d * (1 + y))))
        have hpow_le :
            (1 + y) ^ m ≤ c * Real.exp (d * (1 + y)) :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ c * Real.exp (d * (1 + y)))
            hpow_abs
            (Eq.subst
              (motive := fun x : ℝ => ‖(1 + y) ^ m‖ ≤ c * x)
              hexp_abs
              hy.1)
        have hscale :
            B * (1 + y) ^ m ≤ B * (c * Real.exp (d * (1 + y))) :=
          mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB)
        have hrewrite :
            B * (c * Real.exp (d * (1 + y))) =
              (K / 2) * Real.exp (d * y) := by
          calc
            B * (c * Real.exp (d * (1 + y))) =
                (B * c) * Real.exp (d * (1 + y)) :=
              (mul_assoc B c (Real.exp (d * (1 + y)))).symm
            _ =
                (K / (2 * Real.exp d)) * Real.exp (d * (1 + y)) := by
              have hBc : B * c = K / (2 * Real.exp d) := by
                calc
                  B * c = B * (K / (2 * B * Real.exp d)) := rfl
                  _ = (B * K) / (2 * B * Real.exp d) :=
                    (mul_div_assoc B K (2 * B * Real.exp d)).symm
                  _ = (K * B) / ((2 * Real.exp d) * B) := by
                    exact congrArg₂ (fun x y : ℝ => x / y)
                      (mul_comm B K)
                      (by
                        calc
                          2 * B * Real.exp d = 2 * (B * Real.exp d) :=
                            mul_assoc 2 B (Real.exp d)
                          _ = 2 * (Real.exp d * B) := by
                            exact congrArg (fun x : ℝ => 2 * x)
                              (mul_comm B (Real.exp d))
                          _ = 2 * Real.exp d * B :=
                            (mul_assoc 2 (Real.exp d) B).symm)
                  _ = K / (2 * Real.exp d) := by
                    exact mul_div_mul_right K (2 * Real.exp d) hB.ne'
              exact congrArg
                (fun x : ℝ => x * Real.exp (d * (1 + y)))
                hBc
            _ =
                (K / (2 * Real.exp d)) *
                  (Real.exp d * Real.exp (d * y)) := by
              have harg :
                  d * (1 + y) = d + d * y := by
                calc
                  d * (1 + y) = d * 1 + d * y := mul_add d 1 y
                  _ = d + d * y := by
                    exact congrArg (fun x : ℝ => x + d * y) (mul_one d)
              exact congrArg
                (fun x : ℝ => (K / (2 * Real.exp d)) * x)
                (Eq.trans (congrArg Real.exp harg) (Real.exp_add d (d * y)))
            _ =
                ((K / (2 * Real.exp d)) * Real.exp d) *
                  Real.exp (d * y) :=
              (mul_assoc
                (K / (2 * Real.exp d)) (Real.exp d) (Real.exp (d * y))).symm
            _ =
                (K / 2) * Real.exp (d * y) := by
              have hcancel :
                  (K / (2 * Real.exp d)) * Real.exp d = K / 2 := by
                calc
                  (K / (2 * Real.exp d)) * Real.exp d =
                      K * Real.exp d / (2 * Real.exp d) := by
                    exact div_mul_eq_mul_div K (2 * Real.exp d) (Real.exp d)
                  _ = K * Real.exp d / (Real.exp d * 2) := by
                    exact congrArg (fun x : ℝ => K * Real.exp d / x)
                      (mul_comm 2 (Real.exp d))
                  _ = K / 2 := by
                    calc
                      K * Real.exp d / (Real.exp d * 2) =
                          Real.exp d * K / (Real.exp d * 2) := by
                        exact congrArg (fun x : ℝ => x / (Real.exp d * 2))
                          (mul_comm K (Real.exp d))
                      _ = K / 2 :=
                        mul_div_mul_left K 2 (Real.exp_pos d).ne'
              exact congrArg
                (fun x : ℝ => x * Real.exp (d * y))
                hcancel
        Eq.subst
          (motive := fun x : ℝ => B * (1 + y) ^ m ≤ x)
          hrewrite
          hscale

/-- A finite-order exponential envelope times a positive superexponential
absorber is eventually bounded by its leading constant. -/
theorem finiteOrderEnvelope_mul_exp_absorber_eventually_le_const
    {A B K d : ℝ}
    {m : ℕ}
    (hA : 0 < A)
    (hB : 0 < B)
    (hK : 0 < K)
    (hd : 0 < d) :
    ∀ᶠ y in Filter.atTop,
      A * Real.exp (B * (1 + y) ^ m) *
          Real.exp (-(K * Real.exp (d * y))) ≤ A := by
  have hpoly :
      ∀ᶠ y in Filter.atTop,
        B * (1 + y) ^ m ≤ (K / 2) * Real.exp (d * y) :=
    finiteOrderPolynomialExponent_eventually_le_exp_absorber_half
      hB hK hd
  exact
    hpoly.mono
      fun y hy =>
        have hE_pos : 0 < Real.exp (d * y) :=
          Real.exp_pos (d * y)
        have hhalf_le_full :
            (K / 2) * Real.exp (d * y) ≤ K * Real.exp (d * y) := by
          have hK_half_le : K / 2 ≤ K := by
            have hK_nonneg : 0 ≤ K :=
              le_of_lt hK
            calc
              K / 2 = (1 / 2 : ℝ) * K := by
                exact (one_div_mul_eq_div (a := (2 : ℝ)) (b := K)).symm
              _ ≤ 1 * K := by
                exact mul_le_mul_of_nonneg_right
                  (by
                    exact (div_le_one zero_lt_two).mpr one_le_two)
                  hK_nonneg
              _ = K := one_mul K
          exact mul_le_mul_of_nonneg_right hK_half_le (le_of_lt hE_pos)
        have hexponent_nonpos :
            B * (1 + y) ^ m + -(K * Real.exp (d * y)) ≤ 0 := by
          have hle_full :
              B * (1 + y) ^ m ≤ K * Real.exp (d * y) :=
            le_trans hy hhalf_le_full
          calc
            B * (1 + y) ^ m + -(K * Real.exp (d * y)) ≤
                K * Real.exp (d * y) + -(K * Real.exp (d * y)) :=
              add_le_add_right hle_full (-(K * Real.exp (d * y)))
            _ = 0 := sub_self (K * Real.exp (d * y))
        have hexp_le_one :
            Real.exp (B * (1 + y) ^ m + -(K * Real.exp (d * y))) ≤ 1 :=
          Real.exp_le_one_iff.mpr hexponent_nonpos
        have hproduct_eq :
            Real.exp (B * (1 + y) ^ m) *
                Real.exp (-(K * Real.exp (d * y))) =
              Real.exp (B * (1 + y) ^ m + -(K * Real.exp (d * y))) := by
          exact (Real.exp_add (B * (1 + y) ^ m) (-(K * Real.exp (d * y)))).symm
        have hinner :
            Real.exp (B * (1 + y) ^ m) *
                Real.exp (-(K * Real.exp (d * y))) ≤ 1 :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ 1)
            hproduct_eq.symm
            hexp_le_one
        have hscaled :
            A *
              (Real.exp (B * (1 + y) ^ m) *
                Real.exp (-(K * Real.exp (d * y)))) ≤
              A * 1 :=
          mul_le_mul_of_nonneg_left hinner (le_of_lt hA)
        have hleft_assoc :
            A * Real.exp (B * (1 + y) ^ m) *
                Real.exp (-(K * Real.exp (d * y))) =
              A *
                (Real.exp (B * (1 + y) ^ m) *
                  Real.exp (-(K * Real.exp (d * y)))) :=
          mul_assoc A (Real.exp (B * (1 + y) ^ m))
            (Real.exp (-(K * Real.exp (d * y))))
        have hright_one : A * 1 = A :=
          mul_one A
        Eq.subst
          (motive := fun x : ℝ =>
            A * Real.exp (B * (1 + y) ^ m) *
                Real.exp (-(K * Real.exp (d * y))) ≤ x)
          hright_one
          (Eq.subst
            (motive := fun x : ℝ => x ≤ A * 1)
            hleft_assoc.symm
            hscaled)

/-- Right-boundary upper-tail eventual constant bound for the subcritical
cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_eventually_upperTail_bound
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = b →
        z.im = T →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A := by
  let K : ℝ := ε * (Real.cos (d * ((b - a) / 2)) / 2)
  have hK_pos : 0 < K :=
    verticalStripSubcriticalCosineDamping_rightBoundary_absorberCoeff_pos
      hab hd_pos hd_threshold hε_pos
  have htail :
      ∀ᶠ T in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(K * Real.exp (d * T))) ≤ A :=
    finiteOrderEnvelope_mul_exp_absorber_eventually_le_const
      hA hB hK_pos hd_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hz_im_tail : 1 ≤ z.im :=
          Eq.subst
            (motive := fun x : ℝ => 1 ≤ x)
            hz_im.symm
            hT.2
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          have him_nonneg : 0 ≤ z.im :=
            le_trans zero_le_one hz_im_tail
          have him_norm : ‖z.im‖ = z.im :=
            Real.norm_of_nonneg him_nonneg
          hright z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              him_norm.symm
              hz_im_tail)
        have hraw :
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                    Real.exp (d * z.im))) :=
          verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_le_envelope_mul_exp_absorber
            f hab hd_pos hd_threshold (le_of_lt hε_pos) hz_re hboundary
        have hnorm_im : ‖z.im‖ = z.im :=
          Real.norm_of_nonneg (le_trans zero_le_one hz_im_tail)
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                    Real.exp (d * z.im))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(K * Real.exp (d * T))) := by
          have hcoeff_eq :
              ε * (Real.cos (d * ((b - a) / 2)) / 2) = K := rfl
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              (Eq.trans hnorm_im hz_im))
            (congrArg Real.exp
              (congrArg Neg.neg
                (congrArg₂ (fun x y : ℝ => x * Real.exp (d * y))
                  hcoeff_eq hz_im)))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ A)
            htarget_eq.symm
            hT.1)

/-- Left-boundary upper-tail eventual constant bound for the subcritical
cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_eventually_upperTail_bound
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = a →
        z.im = T →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A := by
  let K : ℝ := ε * (Real.cos (d * (-((b - a) / 2))) / 2)
  have hK_pos : 0 < K :=
    verticalStripSubcriticalCosineDamping_leftBoundary_absorberCoeff_pos
      hab hd_pos hd_threshold hε_pos
  have htail :
      ∀ᶠ T in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(K * Real.exp (d * T))) ≤ A :=
    finiteOrderEnvelope_mul_exp_absorber_eventually_le_const
      hA hB hK_pos hd_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hz_im_tail : 1 ≤ z.im :=
          Eq.subst
            (motive := fun x : ℝ => 1 ≤ x)
            hz_im.symm
            hT.2
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          have him_nonneg : 0 ≤ z.im :=
            le_trans zero_le_one hz_im_tail
          have him_norm : ‖z.im‖ = z.im :=
            Real.norm_of_nonneg him_nonneg
          hleft z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              him_norm.symm
              hz_im_tail)
        have hraw :
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
                    Real.exp (d * z.im))) :=
          verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_le_envelope_mul_exp_absorber
            f hab hd_pos hd_threshold (le_of_lt hε_pos) hz_re hboundary
        have hnorm_im : ‖z.im‖ = z.im :=
          Real.norm_of_nonneg (le_trans zero_le_one hz_im_tail)
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
                    Real.exp (d * z.im))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(K * Real.exp (d * T))) := by
          have hcoeff_eq :
              ε * (Real.cos (d * (-((b - a) / 2))) / 2) = K := rfl
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              (Eq.trans hnorm_im hz_im))
            (congrArg Real.exp
              (congrArg Neg.neg
                (congrArg₂ (fun x y : ℝ => x * Real.exp (d * y))
                  hcoeff_eq hz_im)))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ A)
            htarget_eq.symm
            hT.1)

/-- Right-boundary finite-order envelope transported through the
superexponential lower-tail damping estimate. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_le_envelope_mul_exp_absorber_neg
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = b)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
            Real.exp (-(d * z.im)))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  let envelope : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
  let absorber : ℝ :=
    Real.exp
      (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
        Real.exp (-(d * z.im))))
  have hfactor : ‖g‖ ≤ absorber :=
    verticalStripSubcriticalCosineDampingFactor_rightBoundary_norm_le_exp_neg_exp_neg
      hab hd_pos hd_threshold hε hz
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hfactor_nonneg : 0 ≤ ‖g‖ :=
    norm_nonneg g
  have hfirst :
      ‖f z‖ * ‖g‖ ≤ envelope * ‖g‖ :=
    mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
  have hsecond :
      envelope * ‖g‖ ≤ envelope * absorber :=
    mul_le_mul_of_nonneg_left hfactor
      (le_trans (norm_nonneg (f z)) hboundary)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ envelope * absorber)
      hnorm_mul.symm
      (le_trans hfirst hsecond)

/-- Left-boundary finite-order envelope transported through the
superexponential lower-tail damping estimate. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_le_envelope_mul_exp_absorber_neg
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hz : z.re = a)
    (hboundary :
      ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
        Real.exp
          (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
            Real.exp (-(d * z.im)))) := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  let envelope : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
  let absorber : ℝ :=
    Real.exp
      (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
        Real.exp (-(d * z.im))))
  have hfactor : ‖g‖ ≤ absorber :=
    verticalStripSubcriticalCosineDampingFactor_leftBoundary_norm_le_exp_neg_exp_neg
      hab hd_pos hd_threshold hε hz
  have hnorm_mul :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hfactor_nonneg : 0 ≤ ‖g‖ :=
    norm_nonneg g
  have hfirst :
      ‖f z‖ * ‖g‖ ≤ envelope * ‖g‖ :=
    mul_le_mul_of_nonneg_right hboundary hfactor_nonneg
  have hsecond :
      envelope * ‖g‖ ≤ envelope * absorber :=
    mul_le_mul_of_nonneg_left hfactor
      (le_trans (norm_nonneg (f z)) hboundary)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ envelope * absorber)
      hnorm_mul.symm
      (le_trans hfirst hsecond)

/-- Right-boundary lower-tail eventual constant bound for the subcritical
cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_rightBoundary_eventually_lowerTail_bound
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = b →
        z.im = -T →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A := by
  let K : ℝ := ε * (Real.cos (d * ((b - a) / 2)) / 2)
  have hK_pos : 0 < K :=
    verticalStripSubcriticalCosineDamping_rightBoundary_absorberCoeff_pos
      hab hd_pos hd_threshold hε_pos
  have htail :
      ∀ᶠ T in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(K * Real.exp (d * T))) ≤ A :=
    finiteOrderEnvelope_mul_exp_absorber_eventually_le_const
      hA hB hK_pos hd_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hneg_eq : -z.im = T := by
          calc
            -z.im = -(-T) := by
              exact congrArg Neg.neg hz_im
            _ = T := neg_neg T
        have hz_im_norm : ‖z.im‖ = T := by
          have hneg_nonpos : z.im ≤ 0 :=
            Eq.subst
              (motive := fun x : ℝ => x ≤ 0)
              hz_im.symm
              (neg_nonpos.mpr (le_trans zero_le_one hT.2))
          have hnorm_neg : ‖z.im‖ = -z.im :=
            Real.norm_of_nonpos hneg_nonpos
          exact Eq.trans hnorm_neg hneg_eq
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          hright z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              hz_im_norm.symm
              hT.2)
        have hraw :
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                    Real.exp (-(d * z.im)))) :=
          verticalStripSubcriticalCosineDampedFamily_rightBoundary_norm_le_envelope_mul_exp_absorber_neg
            f hab hd_pos hd_threshold (le_of_lt hε_pos) hz_re hboundary
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                    Real.exp (-(d * z.im)))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(K * Real.exp (d * T))) := by
          have hcoeff_eq :
              ε * (Real.cos (d * ((b - a) / 2)) / 2) = K := rfl
          have hdt :
              -(d * z.im) = d * T := by
            calc
              -(d * z.im) = d * (-z.im) := by
                exact (mul_neg d z.im).symm
              _ = d * T := by
                exact congrArg (fun x : ℝ => d * x) hneg_eq
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              hz_im_norm)
            (congrArg Real.exp
              (congrArg Neg.neg
                (congrArg₂ (fun x y : ℝ => x * Real.exp y) hcoeff_eq hdt)))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ A)
            htarget_eq.symm
            hT.1)

/-- Left-boundary lower-tail eventual constant bound for the subcritical
cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_leftBoundary_eventually_lowerTail_bound
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∀ᶠ T in Filter.atTop,
      ∀ z : ℂ,
        z.re = a →
        z.im = -T →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A := by
  let K : ℝ := ε * (Real.cos (d * (-((b - a) / 2))) / 2)
  have hK_pos : 0 < K :=
    verticalStripSubcriticalCosineDamping_leftBoundary_absorberCoeff_pos
      hab hd_pos hd_threshold hε_pos
  have htail :
      ∀ᶠ T in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) *
            Real.exp (-(K * Real.exp (d * T))) ≤ A :=
    finiteOrderEnvelope_mul_exp_absorber_eventually_le_const
      hA hB hK_pos hd_pos
  have hlarge : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T :=
    eventually_ge_atTop (1 : ℝ)
  exact
    (htail.and hlarge).mono
      fun T hT z hz_re hz_im =>
        have hneg_eq : -z.im = T := by
          calc
            -z.im = -(-T) := by
              exact congrArg Neg.neg hz_im
            _ = T := neg_neg T
        have hz_im_norm : ‖z.im‖ = T := by
          have hneg_nonpos : z.im ≤ 0 :=
            Eq.subst
              (motive := fun x : ℝ => x ≤ 0)
              hz_im.symm
              (neg_nonpos.mpr (le_trans zero_le_one hT.2))
          have hnorm_neg : ‖z.im‖ = -z.im :=
            Real.norm_of_nonpos hneg_nonpos
          exact Eq.trans hnorm_neg hneg_eq
        have hboundary :
            ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) :=
          hleft z hz_re
            (Eq.subst
              (motive := fun x : ℝ => 1 ≤ x)
              hz_im_norm.symm
              hT.2)
        have hraw :
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
              (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
                    Real.exp (-(d * z.im)))) :=
          verticalStripSubcriticalCosineDampedFamily_leftBoundary_norm_le_envelope_mul_exp_absorber_neg
            f hab hd_pos hd_threshold (le_of_lt hε_pos) hz_re hboundary
        have htarget_eq :
            (A * Real.exp (B * (1 + ‖z.im‖) ^ m)) *
                Real.exp
                  (-(ε * (Real.cos (d * (-((b - a) / 2))) / 2) *
                    Real.exp (-(d * z.im)))) =
              A * Real.exp (B * (1 + T) ^ m) *
                Real.exp (-(K * Real.exp (d * T))) := by
          have hcoeff_eq :
              ε * (Real.cos (d * (-((b - a) / 2))) / 2) = K := rfl
          have hdt :
              -(d * z.im) = d * T := by
            calc
              -(d * z.im) = d * (-z.im) := by
                exact (mul_neg d z.im).symm
              _ = d * T := by
                exact congrArg (fun x : ℝ => d * x) hneg_eq
          exact congrArg₂ (fun x y : ℝ => x * y)
            (congrArg
              (fun x : ℝ => A * Real.exp (B * (1 + x) ^ m))
              hz_im_norm)
            (congrArg Real.exp
              (congrArg Neg.neg
                (congrArg₂ (fun x y : ℝ => x * Real.exp y) hcoeff_eq hdt)))
        le_trans hraw
          (Eq.subst
            (motive := fun x : ℝ => x ≤ A)
            htarget_eq.symm
            hT.1)

/-- Upper and lower eventual boundary control, together with compactness of the
remaining bounded-height rectangle, gives a uniform tail boundary package for
the subcritical cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_tail_boundary_package
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) := by
  let hright_upper :=
    verticalStripSubcriticalCosineDampedFamily_rightBoundary_eventually_upperTail_bound
      f hab hd_pos hd_threshold hε_pos hA hB hright
  let hleft_upper :=
    verticalStripSubcriticalCosineDampedFamily_leftBoundary_eventually_upperTail_bound
      f hab hd_pos hd_threshold hε_pos hA hB hleft
  let hright_lower :=
    verticalStripSubcriticalCosineDampedFamily_rightBoundary_eventually_lowerTail_bound
      f hab hd_pos hd_threshold hε_pos hA hB hright
  let hleft_lower :=
    verticalStripSubcriticalCosineDampedFamily_leftBoundary_eventually_lowerTail_bound
      f hab hd_pos hd_threshold hε_pos hA hB hleft
  match eventually_atTop.1 hright_upper,
      eventually_atTop.1 hleft_upper,
      eventually_atTop.1 hright_lower,
      eventually_atTop.1 hleft_lower with
  | ⟨Rru, hru⟩, ⟨Rlu, hlu⟩, ⟨Rrl, hrl⟩, ⟨Rll, hll⟩ =>
      let R : ℝ := max 1 (max Rru (max Rlu (max Rrl Rll)))
      match verticalStripSubcriticalCosineDampedFamily_boundedHeightRectangle_bound
          f a b d ε R hab hhol with
      | ⟨M, hM_pos, hM⟩ =>
          let C : ℝ := max A M
          have hC_pos : 0 < C :=
            lt_of_lt_of_le hA (le_max_left A M)
          have hA_le_C : A ≤ C :=
            le_max_left A M
          have hM_le_C : M ≤ C :=
            le_max_right A M
          have hRru : Rru ≤ R :=
            le_trans (le_max_left Rru (max Rlu (max Rrl Rll)))
              (le_trans (le_max_right 1 (max Rru (max Rlu (max Rrl Rll))))
                (le_of_eq rfl))
          have hRlu : Rlu ≤ R :=
            le_trans
              (le_trans (le_max_left Rlu (max Rrl Rll))
                (le_max_right Rru (max Rlu (max Rrl Rll))))
              (le_max_right 1 (max Rru (max Rlu (max Rrl Rll))))
          have hRrl : Rrl ≤ R :=
            le_trans
              (le_trans
                (le_trans (le_max_left Rrl Rll)
                  (le_max_right Rlu (max Rrl Rll)))
                (le_max_right Rru (max Rlu (max Rrl Rll))))
              (le_max_right 1 (max Rru (max Rlu (max Rrl Rll))))
          have hRll : Rll ≤ R :=
            le_trans
              (le_trans
                (le_trans (le_max_right Rrl Rll)
                  (le_max_right Rlu (max Rrl Rll)))
                (le_max_right Rru (max Rlu (max Rrl Rll))))
              (le_max_right 1 (max Rru (max Rlu (max Rrl Rll))))
          have hR_one : 1 ≤ R :=
            le_max_left 1 (max Rru (max Rlu (max Rrl Rll)))
          have hleft_bound :
              ∀ z : ℂ,
                z.re = a →
                1 ≤ ‖z.im‖ →
                ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
            fun z hz_re hz_tail =>
              match le_total R ‖z.im‖ with
              | Or.inl hlarge =>
                  match le_total 0 z.im with
                  | Or.inl him_nonneg =>
                      have him_norm : ‖z.im‖ = z.im :=
                        Real.norm_of_nonneg him_nonneg
                      have hRle_im : Rlu ≤ z.im :=
                        le_trans hRlu (Eq.subst
                          (motive := fun x : ℝ => R ≤ x)
                          him_norm
                          hlarge)
                      have hraw :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A :=
                        hlu z.im hRle_im z hz_re rfl
                      le_trans hraw hA_le_C
                  | Or.inr him_nonpos =>
                      have him_norm : ‖z.im‖ = -z.im :=
                        Real.norm_of_nonpos him_nonpos
                      have hRle_abs : Rll ≤ ‖z.im‖ :=
                        le_trans hRll hlarge
                      have hz_im_eq :
                          z.im = -‖z.im‖ := by
                        calc
                          z.im = -(-z.im) := (neg_neg z.im).symm
                          _ = -‖z.im‖ := by
                            exact congrArg Neg.neg him_norm.symm
                      have hraw :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A :=
                        hll ‖z.im‖ hRle_abs z hz_re hz_im_eq
                      le_trans hraw hA_le_C
              | Or.inr hmiddle =>
                  have hz_mem :
                      z ∈ verticalStripBoundedHeightRectangle a b R :=
                    ⟨le_of_eq hz_re.symm,
                      le_trans (le_of_eq hz_re) (le_of_lt hab),
                      hmiddle⟩
                  le_trans (hM z hz_mem) hM_le_C
          have hright_bound :
              ∀ z : ℂ,
                z.re = b →
                1 ≤ ‖z.im‖ →
                ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
            fun z hz_re hz_tail =>
              match le_total R ‖z.im‖ with
              | Or.inl hlarge =>
                  match le_total 0 z.im with
                  | Or.inl him_nonneg =>
                      have him_norm : ‖z.im‖ = z.im :=
                        Real.norm_of_nonneg him_nonneg
                      have hRle_im : Rru ≤ z.im :=
                        le_trans hRru (Eq.subst
                          (motive := fun x : ℝ => R ≤ x)
                          him_norm
                          hlarge)
                      have hraw :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A :=
                        hru z.im hRle_im z hz_re rfl
                      le_trans hraw hA_le_C
                  | Or.inr him_nonpos =>
                      have him_norm : ‖z.im‖ = -z.im :=
                        Real.norm_of_nonpos him_nonpos
                      have hRle_abs : Rrl ≤ ‖z.im‖ :=
                        le_trans hRrl hlarge
                      have hz_im_eq :
                          z.im = -‖z.im‖ := by
                        calc
                          z.im = -(-z.im) := (neg_neg z.im).symm
                          _ = -‖z.im‖ := by
                            exact congrArg Neg.neg him_norm.symm
                      have hraw :
                          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ A :=
                        hrl ‖z.im‖ hRle_abs z hz_re hz_im_eq
                      le_trans hraw hA_le_C
              | Or.inr hmiddle =>
                  have hz_mem :
                      z ∈ verticalStripBoundedHeightRectangle a b R :=
                    ⟨le_trans (le_of_lt hab) (le_of_eq hz_re.symm),
                      le_of_eq hz_re,
                      hmiddle⟩
                  le_trans (hM z hz_mem) hM_le_C
          exact ⟨C, hC_pos, hleft_bound, hright_bound⟩

/-- The subcritical cosine-damping exponent has nonpositive real part on the
closed strip. -/
theorem verticalStripSubcriticalCosineDampingExponent_re_nonpos_on_closedStrip
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z).re ≤ 0 := by
  have hkernel_pos :
      0 < (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineBarrierKernel_re_pos_on_closedStrip
      hab hd_pos hd_threshold hza hzb
  have hkernel_nonneg :
      0 ≤ (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    le_of_lt hkernel_pos
  have hmul_nonneg :
      0 ≤ ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    mul_nonneg hε hkernel_nonneg
  have hneg_nonpos :
      -(ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re) ≤ 0 :=
    neg_nonpos.mpr hmul_nonneg
  have hre :
      (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re :=
    verticalStripSubcriticalCosineDampingExponent_re_eq_neg_mul a b d ε z
  have hmul :
      -ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re =
        -(ε * (verticalStripSubcriticalCosineBarrierKernel a b d z).re) :=
    neg_mul ε (verticalStripSubcriticalCosineBarrierKernel a b d z).re
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 0)
      (Eq.trans hre hmul).symm
      hneg_nonpos

/-- The subcritical holomorphic damping factor is bounded by one on the whole
closed strip. -/
theorem verticalStripSubcriticalCosineDampingFactor_norm_le_one_on_closedStrip
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖Complex.exp
        (-((ε : ℝ) : ℂ) *
          verticalStripSubcriticalCosineBarrierKernel a b d z)‖ ≤ 1 := by
  let w : ℂ :=
    -((ε : ℝ) : ℂ) *
      verticalStripSubcriticalCosineBarrierKernel a b d z
  have hre_nonpos : w.re ≤ 0 :=
    verticalStripSubcriticalCosineDampingExponent_re_nonpos_on_closedStrip
      hab hd_pos hd_threshold hε hza hzb
  have hexp_le_one : Real.exp w.re ≤ 1 :=
    Real.exp_le_one_iff.mpr hre_nonpos
  have hnorm : ‖Complex.exp w‖ = Real.exp w.re :=
    complexNorm_exp_eq_realExp_re w
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      hnorm.symm
      hexp_le_one

/-- Multiplication by the subcritical holomorphic damping factor can only
decrease norms on the closed strip. -/
theorem verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
    (f : ℂ → ℂ)
    {a b d ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (z : ℂ)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
      ‖f z‖ := by
  let g : ℂ :=
    Complex.exp
      (-((ε : ℝ) : ℂ) *
        verticalStripSubcriticalCosineBarrierKernel a b d z)
  have hfactor : ‖g‖ ≤ 1 :=
    verticalStripSubcriticalCosineDampingFactor_norm_le_one_on_closedStrip
      hab hd_pos hd_threshold hε z hza hzb
  have hmul_eq :
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
        ‖f z‖ * ‖g‖ := by
    calc
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ =
          ‖f z * g‖ := by
        rfl
      _ = ‖f z‖ * ‖g‖ := by
        exact norm_mul (f z) g
  have hscale_nonneg : 0 ≤ ‖f z‖ :=
    norm_nonneg (f z)
  have hscaled : ‖f z‖ * ‖g‖ ≤ ‖f z‖ * 1 :=
    mul_le_mul_of_nonneg_left hfactor hscale_nonneg
  have hright : ‖f z‖ * 1 = ‖f z‖ :=
    mul_one ‖f z‖
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ x)
      hright
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖f z‖ * 1)
        hmul_eq.symm
        hscaled)

/-- Boundary finite-order envelopes transport through the subcritical
holomorphic damping factor on the upper vertical tail. -/
theorem verticalStripSubcriticalCosineDampedFamily_upperTail_boundary_envelope
    (f : ℂ → ℂ)
    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε : 0 ≤ ε)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    (∀ z : ℂ,
      z.re = a →
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  exact
    ⟨fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_of_eq hz_re.symm
        have hzb : z.re ≤ b :=
          le_trans (le_of_eq hz_re) (le_of_lt hab)
        le_trans
          (verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
            f hab hd_pos hd_threshold hε z hza hzb)
          (hleft z hz_re hz_im),
      fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
        have hzb : z.re ≤ b :=
          le_of_eq hz_re
        le_trans
          (verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
            f hab hd_pos hd_threshold hε z hza hzb)
          (hright z hz_re hz_im)⟩

/-- Boundary finite-order envelopes transport through the upper-tail tilted
damping factor on the upper vertical tail. -/
theorem verticalStripUpperTailDampedFamily_upperTail_boundary_envelope
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε : 0 ≤ ε)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    (∀ z : ℂ,
      z.re = a →
      1 ≤ z.im →
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ z.im →
      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  exact
    ⟨fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_of_eq hz_re.symm
        have hzb : z.re ≤ b :=
          le_trans (le_of_eq hz_re) (le_of_lt hab)
        le_trans
          (verticalStripUpperTailDampedFamily_norm_le_original_on_closedStrip
            f a b ε hε z hza hzb)
          (hleft z hz_re hz_im),
      fun z hz_re hz_im =>
        have hza : a ≤ z.re :=
          le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
        have hzb : z.re ≤ b :=
          le_of_eq hz_re
        le_trans
          (verticalStripUpperTailDampedFamily_norm_le_original_on_closedStrip
            f a b ε hε z hza hzb)
          (hright z hz_re hz_im)⟩




end
end LFunctions
end Boundary
