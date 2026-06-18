import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaEndpointCapCollars.Foundation.Owner

/-!
# Left endpoint cap-collar domains and Cauchy-Goursat theorems

Definitions and theorems for the left endpoint cap-collar domain and its boundary
analysis, corresponding to the endpoint pole at zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Helper: Equivalence between pure exponential and circleMap at origin. -/
private lemma leftCapCollar_exp_eq_circleMap (ρ θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      circleMap (0 : ℂ) ρ θ :=
  let h1 : (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
    congrArg (fun e => (ρ : ℂ) * e) (congrArg Complex.exp (mul_comm Complex.I (θ : ℂ)))
  Eq.trans h1 (zero_add ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).symm

def Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain
    (T ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball (0 : ℂ) ρ

/-- Membership in the left endpoint cap/collar domain is coordinatewise
membership in the endpoint rectangular cap plus avoidance of the deleted
endpoint disk. -/
theorem Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ↔
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ :=
  ⟨fun hz => ⟨hz.1.1, hz.1.2, hz.2⟩,
   fun hz => ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩⟩

/-- A point in the left endpoint cap rectangle, after deleting the endpoint
disk, avoids every deleted integer disk in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (_hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre : z.re ∈ [[(0 : ℝ), ρ]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball (0 : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ :=
  if hmzero : m = 0 then
    let hball_eq : Metric.ball ((m : ℕ) : ℂ) ρ = Metric.ball (0 : ℂ) ρ :=
      congrArg (fun c : ℂ => Metric.ball c ρ)
        (Eq.trans (congrArg (fun k : ℕ => (k : ℂ)) hmzero)
          (Nat.cast_zero : ((0 : ℕ) : ℂ) = 0))
    hball_eq.symm ▸ hzcentral
  else fun hzball =>
    let hm_pos := Nat.pos_of_ne_zero hmzero
    let hone_le_m := Real.one_le_natCast_of_pos hm_pos
    let hρ_lt_half := Real.lt_one_div_two_of_lt_one_div_four hρquarter
    let hzIcc := Real.endpoint_bounds_of_mem_uIcc hρnonneg hzre
    let hzre_le := hzIcc.2
    let hdist_lt := Complex.endpoint_norm_lt_of_mem_ball z (m : ℂ) hzball
    let hre_norm := Complex.abs_re_le_abs (z - (m : ℂ))
    let hreal := Real.endpoint_left_re_sub_integer_le_neg_radius hzre_le hone_le_m hρ_lt_half
    let hre_le_neg : (z - (m : ℂ)).re ≤ -ρ :=
      (Complex.endpoint_sub_natCast_re z m).symm ▸ hreal
    let hneg : ρ ≤ -((z - (m : ℂ)).re) := (neg_neg ρ) ▸ neg_le_neg hre_le_neg
    let hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| := hneg.trans (neg_le_abs _)
    not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The closed left endpoint cap rectangle lies in the ambient finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T :=
  fun z hz =>
    let hzIcc := Real.endpoint_bounds_of_mem_uIcc hρnonneg hz.1
    let hρ_lt_one := Real.lt_one_of_lt_one_div_four hρquarter
    let hone_le : (1 : ℝ) ≤ (N : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg N)
    Complex.mem_reProdIm.mpr
      ⟨⟨hzIcc.1, (hzIcc.2.trans (le_of_lt hρ_lt_one)).trans hone_le⟩, hz.2⟩

/-- The left endpoint cap/collar domain lies in the finite Abel-Plana
punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ :=
  fun z hz =>
    let hzdata := Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mp hz
    let hclosed :=
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
        hρnonneg hρquarter ⟨hzdata.1, hzdata.2.1⟩
    let havoid : ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := fun m hm =>
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
        hm hρnonneg hρquarter hzdata.1 hzdata.2.1 hzdata.2.2
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr ⟨hclosed, havoid⟩

/-- Continuity of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
  hcont.mono
    (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
      T hρnonneg hρquarter)

/-- Holomorphy of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
  hdiff.mono
    (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
      T hρnonneg hρquarter)

/-- A point on the right semicircle around the left endpoint lies in the
left endpoint punctured cap/collar domain.

This is the endpoint-specific geometric fact that replaces the false full-disk
containment statement: only the right semicircle, not the whole disk, belongs
to the left cap. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSemicirclePoint_mem_capCollar
    {T ρ θ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hθ : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
  let hρnonneg : 0 ≤ ρ := le_of_lt hρ
  let hexp : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) :=
    congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  let hre :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) =
        ρ * Real.cos θ :=
    Eq.trans (Complex.re_ofReal_mul ρ (Complex.exp (Complex.I * (θ : ℂ))))
      (congrArg (ρ * ·)
        (Eq.trans (congrArg Complex.re hexp) (Complex.exp_ofReal_mul_I_re θ)))
  let him :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) =
        ρ * Real.sin θ :=
    Eq.trans (Complex.im_ofReal_mul ρ (Complex.exp (Complex.I * (θ : ℂ))))
      (congrArg (ρ * ·)
        (Eq.trans (congrArg Complex.im hexp) (Complex.exp_ofReal_mul_I_im θ)))
  let hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθ
  let hre_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[(0 : ℝ), ρ]] :=
    let hleft : 0 ≤ ρ * Real.cos θ := mul_nonneg hρnonneg hcos_nonneg
    let hright : ρ * Real.cos θ ≤ ρ :=
      mul_le_of_le_one_right hρnonneg (Real.cos_le_one θ)
    Eq.mp
      (congrArg
        (fun x : ℝ => x ∈ [[(0 : ℝ), ρ]])
        hre.symm)
      (Real.endpoint_mem_uIcc_of_bounds hρnonneg (And.intro hleft hright))
  let hsin_abs : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
  let him_abs : |ρ * Real.sin θ| ≤ ρ :=
    let e1 : |ρ * Real.sin θ| = ρ * |Real.sin θ| :=
      Eq.trans (abs_mul ρ (Real.sin θ))
        (congrArg (· * |Real.sin θ|) (abs_of_nonneg hρnonneg))
    let l1 : ρ * |Real.sin θ| ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
    (Eq.le e1).trans (l1.trans (Eq.le (mul_one ρ)))
  let him_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] :=
    let habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    let hb := abs_le.mp habsT
    Eq.mp
      (congrArg
        (fun y : ℝ => y ∈ [[-T, T]])
        him.symm)
      (Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) hb)
  let hz_eq :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      circleMap (0 : ℂ) ρ θ :=
    leftCapCollar_exp_eq_circleMap ρ θ
  let hnot_ball :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∉
        Metric.ball (0 : ℂ) ρ := hz_eq ▸ circleMap_not_mem_ball (0 : ℂ) ρ θ
  Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
    ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the left principal-value vertical side belong to the left
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointPVVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, -ρ]] ∨ y ∈ [[ρ, T]]) :
    (Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
  let hρnonneg : 0 ≤ ρ := le_of_lt hρ
  let hIyre : (Complex.I * (y : ℂ)).re = 0 :=
    Eq.trans (Complex.I_mul_re (y : ℂ))
      (Eq.trans (congrArg Neg.neg (Complex.ofReal_im y)) neg_zero)
  let hIyim : (Complex.I * (y : ℂ)).im = y :=
    Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
  let hre_mem :
      (Complex.I * (y : ℂ)).re ∈ [[(0 : ℝ), ρ]] :=
    Real.endpoint_mem_uIcc_congr hIyre
      (Real.endpoint_mem_uIcc_of_bounds hρnonneg (And.intro le_rfl hρnonneg))
  let him_mem :
      (Complex.I * (y : ℂ)).im ∈ [[-T, T]] :=
    Real.endpoint_mem_uIcc_congr hIyim
      (match hy with
       | Or.inl hy =>
           let hyIcc := Set.mem_Icc.mp hy
           let hleT := hyIcc.2.trans (Real.endpoint_neg_radius_le_height hT hρ)
           Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) ⟨hyIcc.1, hleT⟩
       | Or.inr hy =>
           let hyIcc := Set.mem_Icc.mp hy
           let hge_negT := (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
           Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) ⟨hge_negT, hyIcc.2⟩)
  let hnot_ball :
      (Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ :=
    fun hball =>
      let hdist := Complex.endpoint_norm_lt_of_mem_ball (Complex.I * (y : ℂ)) (0 : ℂ) hball
      let hρ_le_abs_y : ρ ≤ |y| :=
        match hy with
        | Or.inl hy =>
            let hb := (Set.mem_Icc.mp hy).2
            ((neg_neg ρ) ▸ neg_le_neg hb : ρ ≤ -y).trans (neg_le_abs y)
        | Or.inr hy =>
            (Set.mem_Icc.mp hy).1.trans (le_abs_self y)
      let hnorm : ‖Complex.I * (y : ℂ)‖ = |y| :=
        Eq.trans (norm_mul Complex.I (y : ℂ))
          (Eq.trans (congrArg (· * ‖(y : ℂ)‖) Complex.norm_I)
            (Eq.trans (one_mul ‖(y : ℂ)‖)
              (Eq.trans (Complex.norm_real y) (Real.norm_eq_abs y))))
      let hlt : ‖Complex.I * (y : ℂ)‖ < ρ := (sub_zero (Complex.I * (y : ℂ))) ▸ hdist
      let hlt_abs : |y| < ρ := hnorm ▸ hlt
      not_lt_of_ge hρ_le_abs_y hlt_abs
  Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
    ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the safe vertical side `Re z = ρ` belong to the left endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, T]]) :
    ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
  let hρnonneg := le_of_lt hρ
  let hIyre : (Complex.I * (y : ℂ)).re = 0 :=
    Eq.trans (Complex.I_mul_re (y : ℂ))
      (Eq.trans (congrArg Neg.neg (Complex.ofReal_im y)) neg_zero)
  let hIyim : (Complex.I * (y : ℂ)).im = y :=
    Eq.trans (Complex.I_mul_im (y : ℂ)) (Complex.ofReal_re y)
  let hre : ((ρ : ℂ) + Complex.I * (y : ℂ)).re = ρ :=
    Eq.trans (Complex.add_re (ρ : ℂ) (Complex.I * (y : ℂ)))
      (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_re ρ) hIyre) (add_zero ρ))
  let him : ((ρ : ℂ) + Complex.I * (y : ℂ)).im = y :=
    Eq.trans (Complex.add_im (ρ : ℂ) (Complex.I * (y : ℂ)))
      (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_im ρ) hIyim) (zero_add y))
  let hre_mem : ((ρ : ℂ) + Complex.I * (y : ℂ)).re ∈ [[(0 : ℝ), ρ]] :=
    Real.endpoint_mem_uIcc_congr hre
      (Real.endpoint_mem_uIcc_of_bounds hρnonneg (And.intro hρnonneg le_rfl))
  let him_mem : ((ρ : ℂ) + Complex.I * (y : ℂ)).im ∈ [[-T, T]] :=
    Real.endpoint_mem_uIcc_congr him hy
  let hnot_ball : ((ρ : ℂ) + Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ :=
    fun hball =>
      let hdist := Complex.endpoint_norm_lt_of_mem_ball ((ρ : ℂ) + Complex.I * (y : ℂ)) (0 : ℂ) hball
      let hre_norm := Complex.endpoint_abs_re_le_norm ((ρ : ℂ) + Complex.I * (y : ℂ))
      let hre_abs : |((ρ : ℂ) + Complex.I * (y : ℂ)).re| = ρ :=
        Eq.trans (congrArg abs hre) (abs_of_nonneg hρnonneg)
      let hρ_le_norm : ρ ≤ ‖(ρ : ℂ) + Complex.I * (y : ℂ)‖ := hre_abs.ge.trans hre_norm
      let hlt : ‖(ρ : ℂ) + Complex.I * (y : ℂ)‖ < ρ :=
        (sub_zero ((ρ : ℂ) + Complex.I * (y : ℂ))) ▸ hdist
      not_lt_of_ge hρ_le_norm hlt
  Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr ⟨hre_mem, him_mem, hnot_ball⟩

/-- The lower left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `-T ≤ Im z ≤ -ρ` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) - Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[(-T), (-ρ)]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
  fun z hz =>
    let hzre := (Complex.mem_reProdIm.mp hz).1
    let hzim_lower := (Complex.mem_reProdIm.mp hz).2
    let hIρre : (Complex.I * (ρ : ℂ)).re = 0 :=
      Eq.trans (Complex.I_mul_re (ρ : ℂ))
        (Eq.trans (congrArg Neg.neg (Complex.ofReal_im ρ)) neg_zero)
    let he_re1 : ((ρ : ℂ) - Complex.I * (ρ : ℂ)).re = ρ :=
      Eq.trans (Complex.sub_re (ρ : ℂ) (Complex.I * (ρ : ℂ)))
        (Eq.trans (congrArg₂ (· - ·) (Complex.ofReal_re ρ) hIρre) (sub_zero ρ))
    let hb := Set.mem_Icc.mp hzre
    let hzre' : z.re ∈ [[(0 : ℝ), ρ]] :=
      Set.mem_Icc.mpr ⟨Complex.zero_re ▸ hb.1, he_re1 ▸ hb.2⟩
    let horder := Real.endpoint_neg_height_le_neg_radius hρT
    let hzimIcc := Real.endpoint_bounds_of_mem_uIcc horder hzim_lower
    let hleT := hzimIcc.2.trans (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
    let hzim : z.im ∈ [[-T, T]] :=
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        ⟨hzimIcc.1, hleT⟩
    let hneg : ρ ≤ -z.im := (neg_neg ρ) ▸ Real.endpoint_neg_le_neg_of_le hzimIcc.2
    let hρ_le_abs_im : ρ ≤ |z.im| := hneg.trans (neg_le_abs z.im)
    let hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ :=
      Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im hρ_le_abs_im
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr ⟨hzre', hzim, hnot_ball⟩

/-- The upper left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `ρ ≤ Im z ≤ T` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) + Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[ρ, T]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
  fun z hz =>
    let hzre := (Complex.mem_reProdIm.mp hz).1
    let hzim_upper := (Complex.mem_reProdIm.mp hz).2
    let hIρre : (Complex.I * (ρ : ℂ)).re = 0 :=
      Eq.trans (Complex.I_mul_re (ρ : ℂ))
        (Eq.trans (congrArg Neg.neg (Complex.ofReal_im ρ)) neg_zero)
    let he_re1 : ((ρ : ℂ) + Complex.I * (ρ : ℂ)).re = ρ :=
      Eq.trans (Complex.add_re (ρ : ℂ) (Complex.I * (ρ : ℂ)))
        (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_re ρ) hIρre) (add_zero ρ))
    let hb := Set.mem_Icc.mp hzre
    let hzre' : z.re ∈ [[(0 : ℝ), ρ]] :=
      Set.mem_Icc.mpr ⟨Complex.zero_re ▸ hb.1, he_re1 ▸ hb.2⟩
    let horder := le_of_lt hρT
    let hzimIcc := Real.endpoint_bounds_of_mem_uIcc horder hzim_upper
    let hge_negT := (Real.endpoint_neg_height_le_radius (hρ.trans hρT) hρ).trans hzimIcc.1
    let hzim : z.im ∈ [[-T, T]] :=
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        ⟨hge_negT, hzimIcc.2⟩
    let hρ_le_abs_im : ρ ≤ |z.im| := hzimIcc.1.trans (le_abs_self z.im)
    let hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ :=
      Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im hρ_le_abs_im
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr ⟨hzre', hzim, hnot_ball⟩

/-! ### Coordinate helpers for the rectangle-boundary transport -/

private lemma I_mul_ofReal_re (r : ℝ) : (Complex.I * (r : ℂ)).re = 0 :=
  Eq.trans (Complex.I_mul_re (r : ℂ))
    (Eq.trans (congrArg Neg.neg (Complex.ofReal_im r)) neg_zero)
private lemma I_mul_ofReal_im (r : ℝ) : (Complex.I * (r : ℂ)).im = r :=
  Eq.trans (Complex.I_mul_im (r : ℂ)) (Complex.ofReal_re r)
private lemma negI_mul_re (r : ℝ) : (-Complex.I * (r : ℂ)).re = 0 :=
  Eq.trans (congrArg Complex.re (neg_mul Complex.I (r : ℂ)))
    (Eq.trans (Complex.neg_re (Complex.I * (r : ℂ))) (congrArg Neg.neg (I_mul_ofReal_re r)) |>.trans
      neg_zero)
private lemma negI_mul_im (r : ℝ) : (-Complex.I * (r : ℂ)).im = -r :=
  Eq.trans (congrArg Complex.im (neg_mul Complex.I (r : ℂ)))
    (Eq.trans (Complex.neg_im (Complex.I * (r : ℂ))) (congrArg Neg.neg (I_mul_ofReal_im r)))
private lemma ofReal_sub_I_mul_re (a r : ℝ) :
    ((a : ℂ) - Complex.I * (r : ℂ)).re = a :=
  Eq.trans (Complex.sub_re (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· - ·) (Complex.ofReal_re a) (I_mul_ofReal_re r)) (sub_zero a))
private lemma ofReal_sub_I_mul_im (a r : ℝ) :
    ((a : ℂ) - Complex.I * (r : ℂ)).im = -r :=
  Eq.trans (Complex.sub_im (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· - ·) (Complex.ofReal_im a) (I_mul_ofReal_im r)) (zero_sub r))
private lemma ofReal_add_I_mul_re (a r : ℝ) :
    ((a : ℂ) + Complex.I * (r : ℂ)).re = a :=
  Eq.trans (Complex.add_re (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_re a) (I_mul_ofReal_re r)) (add_zero a))
private lemma ofReal_add_I_mul_im (a r : ℝ) :
    ((a : ℂ) + Complex.I * (r : ℂ)).im = r :=
  Eq.trans (Complex.add_im (a : ℂ) (Complex.I * (r : ℂ)))
    (Eq.trans (congrArg₂ (· + ·) (Complex.ofReal_im a) (I_mul_ofReal_im r)) (zero_add r))

/-- Lower horizontal integrand normalization: `f (x + ↑(-r)·I) = f (x - I·r)`. -/
private lemma left_lower_integrand (f : ℂ → ℂ) (r : ℝ) :
    (fun x : ℝ => f ((x : ℂ) + ((-r : ℝ) : ℂ) * Complex.I)) =
      (fun x : ℝ => f ((x : ℂ) - Complex.I * (r : ℂ))) :=
  funext fun x =>
    congrArg f
      (Eq.trans
        (congrArg (fun w => (x : ℂ) + w)
          (Eq.trans (congrArg (· * Complex.I) (Complex.ofReal_neg r))
            (Eq.trans (neg_mul (r : ℂ) Complex.I)
              (congrArg Neg.neg (mul_comm (r : ℂ) Complex.I)))))
        (sub_eq_add_neg (x : ℂ) (Complex.I * (r : ℂ))).symm)
/-- Upper horizontal integrand normalization: `f (x + ↑r·I) = f (x + I·r)`. -/
private lemma left_upper_integrand (f : ℂ → ℂ) (r : ℝ) :
    (fun x : ℝ => f ((x : ℂ) + (r : ℂ) * Complex.I)) =
      (fun x : ℝ => f ((x : ℂ) + Complex.I * (r : ℂ))) :=
  funext fun x =>
    congrArg f (congrArg (fun w => (x : ℂ) + w) (mul_comm (r : ℂ) Complex.I))
/-- Safe vertical integrand normalization: `f (↑a + ↑y·I) = f (a + I·y)`. -/
private lemma left_vert_integrand (f : ℂ → ℂ) (a : ℝ) :
    (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f ((a : ℂ) + Complex.I * (y : ℂ))) :=
  funext fun y =>
    congrArg f (congrArg (fun w => (a : ℂ) + w) (mul_comm (y : ℂ) Complex.I))
/-- Principal-value vertical integrand normalization: `f (↑0 + ↑y·I) = f (I·y)`. -/
private lemma left_pv_integrand (f : ℂ → ℂ) :
    (fun y : ℝ => f (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f (Complex.I * (y : ℂ))) :=
  funext fun y =>
    congrArg f
      (Eq.trans (congrArg (· + (y : ℂ) * Complex.I) Complex.ofReal_zero)
        (Eq.trans (zero_add ((y : ℂ) * Complex.I)) (mul_comm (y : ℂ) Complex.I)))

/-- Congruence of an interval integral in integrand and both endpoints. -/
private lemma intervalIntegral_congr3 {g g' : ℝ → ℂ} {a a' b b' : ℝ}
    (hg : g = g') (ha : a = a') (hb : b = b') :
    (∫ x : ℝ in a..b, g x) = ∫ x : ℝ in a'..b', g' x :=
  Eq.trans (congrArg (fun w => intervalIntegral w a b MeasureTheory.volume) hg)
    (Eq.trans (congrArg (fun w => intervalIntegral g' w b MeasureTheory.volume) ha)
      (congrArg (fun w => intervalIntegral g' a' w MeasureTheory.volume) hb))

/-- Coordinate normalization for the lower left endpoint rectangle boundary. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_normalize_rectBoundary
    (f : ℂ → ℂ)
    (T ρ : ℝ)
    (hrect :
      (∫ x : ℝ in (-Complex.I * (T : ℂ)).re..
          (((ρ : ℂ) - Complex.I * (ρ : ℂ)).re),
          f ((x : ℂ) + ((-Complex.I * (T : ℂ)).im : ℂ) * Complex.I)) -
          (∫ x : ℝ in (-Complex.I * (T : ℂ)).re..
            (((ρ : ℂ) - Complex.I * (ρ : ℂ)).re),
            f ((x : ℂ) + ((((ρ : ℂ) - Complex.I * (ρ : ℂ)).im) : ℂ) *
              Complex.I)) +
            Complex.I •
              (∫ y : ℝ in (-Complex.I * (T : ℂ)).im..
                (((ρ : ℂ) - Complex.I * (ρ : ℂ)).im),
                f (((((ρ : ℂ) - Complex.I * (ρ : ℂ)).re) : ℂ) +
                  (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (-Complex.I * (T : ℂ)).im..
                  (((ρ : ℂ) - Complex.I * (ρ : ℂ)).im),
                  f (((-Complex.I * (T : ℂ)).re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 :=
  let hIA := intervalIntegral_congr3
    (Eq.trans (left_lower_integrand f T).symm
      (congrArg (fun v : ℝ => fun x : ℝ => f ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I))
        (negI_mul_im T).symm))
    (negI_mul_re T).symm (ofReal_sub_I_mul_re ρ ρ).symm
  let hIB := intervalIntegral_congr3
    (Eq.trans (left_lower_integrand f ρ).symm
      (congrArg (fun v : ℝ => fun x : ℝ => f ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I))
        (ofReal_sub_I_mul_im ρ ρ).symm))
    (negI_mul_re T).symm (ofReal_sub_I_mul_re ρ ρ).symm
  let hIC := intervalIntegral_congr3
    (Eq.trans (left_vert_integrand f ρ).symm
      (congrArg (fun v : ℝ => fun y : ℝ => f (((v : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        (ofReal_sub_I_mul_re ρ ρ).symm))
    (negI_mul_im T).symm (ofReal_sub_I_mul_im ρ ρ).symm
  let hID := intervalIntegral_congr3
    (Eq.trans (left_pv_integrand f).symm
      (congrArg (fun v : ℝ => fun y : ℝ => f (((v : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        (negI_mul_re T).symm))
    (negI_mul_im T).symm (ofReal_sub_I_mul_im ρ ρ).symm
  Eq.trans
    (congrArg₂ (· - ·)
      (congrArg₂ (· + ·) (congrArg₂ (· - ·) hIA hIB) (congrArg (HMul.hMul Complex.I) hIC))
      (congrArg (HMul.hMul Complex.I) hID))
    hrect

/-- Cauchy-Goursat on the lower ordinary rectangle in the left endpoint cap.

This is the lower rectangular piece of the classical endpoint indentation
argument.  The remaining endpoint cap theorem is obtained by adding this to
the corresponding upper rectangle and the circular cap deformation. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 :=
  let z₀ : ℂ := -Complex.I * (T : ℂ)
  let z₁ : ℂ := (ρ : ℂ) - Complex.I * (ρ : ℂ)
  let hz0re : z₀.re = (0 : ℂ).re := Eq.trans (negI_mul_re T) Complex.zero_re.symm
  let hz0im : z₀.im = -T := negI_mul_im T
  let hz1im : z₁.im = -ρ := ofReal_sub_I_mul_im ρ ρ
  let hzre : z₀.re ≤ z₁.re :=
    (negI_mul_re T).le.trans (hρ.le.trans (ofReal_sub_I_mul_re ρ ρ).ge)
  let hzim : z₀.im ≤ z₁.im :=
    hz0im.le.trans ((neg_le_neg hρT.le).trans hz1im.ge)
  let hclosed := Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar hT hρ hρT
  let hReEq : Set.uIcc z₀.re z₁.re = Set.Icc ((0 : ℂ).re) z₁.re :=
    Eq.trans (Set.uIcc_of_le hzre) (congrArg (fun w => Set.Icc w z₁.re) hz0re)
  let hImEq : Set.uIcc z₀.im z₁.im = Set.Icc (-T) (-ρ) :=
    Eq.trans (Set.uIcc_of_le hzim) (congrArg₂ Set.Icc hz0im hz1im)
  let Hc : ContinuousOn f (Set.uIcc z₀.re z₁.re ×ℂ Set.uIcc z₀.im z₁.im) :=
    (congrArg₂ (· ×ℂ ·) hReEq hImEq).symm ▸ hcont.mono hclosed
  let hsubD : (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
      Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
    fun z hz =>
      let hzd := Complex.mem_reProdIm.mp hz
      let h1 := Set.mem_Ioo.mp hzd.1
      let h2 := Set.mem_Ioo.mp hzd.2
      let hre : z.re ∈ Set.Icc ((0 : ℂ).re) z₁.re :=
        Set.mem_Icc.mpr
          ⟨hz0re.symm.trans_le ((min_eq_left hzre).symm.trans_le (le_of_lt h1.1)),
            (le_of_lt h1.2).trans_eq (max_eq_right hzre)⟩
      let him : z.im ∈ Set.Icc (-T) (-ρ) :=
        Set.mem_Icc.mpr
          ⟨hz0im.symm.trans_le ((min_eq_left hzim).symm.trans_le (le_of_lt h2.1)),
            (le_of_lt h2.2).trans_eq ((max_eq_right hzim).trans hz1im)⟩
      hclosed (Complex.mem_reProdIm.mpr ⟨hre, him⟩)
  Complex.leftEndpointLowerRectangleBoundaryIntegral_normalize_rectBoundary f T ρ
    (Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ Hc (hdiff.mono hsubD))

/-- Cauchy-Goursat on the upper ordinary rectangle in the left endpoint cap. -/
theorem Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
          Complex.I *
            (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
      0 :=
  let z₀ : ℂ := Complex.I * (ρ : ℂ)
  let z₁ : ℂ := (ρ : ℂ) + Complex.I * (T : ℂ)
  let hz0re : z₀.re = (0 : ℂ).re := Eq.trans (I_mul_ofReal_re ρ) Complex.zero_re.symm
  let hz0im : z₀.im = ρ := I_mul_ofReal_im ρ
  let hz1re : z₁.re = ((ρ : ℂ) + Complex.I * (ρ : ℂ)).re :=
    Eq.trans (ofReal_add_I_mul_re ρ T) (ofReal_add_I_mul_re ρ ρ).symm
  let hz1im : z₁.im = T := ofReal_add_I_mul_im ρ T
  let hzre : z₀.re ≤ z₁.re :=
    (I_mul_ofReal_re ρ).le.trans (hρ.le.trans (ofReal_add_I_mul_re ρ T).ge)
  let hzim : z₀.im ≤ z₁.im :=
    (I_mul_ofReal_im ρ).le.trans (hρT.le.trans (ofReal_add_I_mul_im ρ T).ge)
  let hclosed := Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar hρ hρT
  let hReEq : Set.uIcc z₀.re z₁.re = Set.Icc ((0 : ℂ).re) (((ρ : ℂ) + Complex.I * (ρ : ℂ)).re) :=
    Eq.trans (Set.uIcc_of_le hzre) (congrArg₂ Set.Icc hz0re hz1re)
  let hImEq : Set.uIcc z₀.im z₁.im = Set.Icc ρ T :=
    Eq.trans (Set.uIcc_of_le hzim) (congrArg₂ Set.Icc hz0im hz1im)
  let Hc : ContinuousOn f (Set.uIcc z₀.re z₁.re ×ℂ Set.uIcc z₀.im z₁.im) :=
    (congrArg₂ (· ×ℂ ·) hReEq hImEq).symm ▸ hcont.mono hclosed
  let hsubD : (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
      Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ :=
    fun z hz =>
      let hzd := Complex.mem_reProdIm.mp hz
      let h1 := Set.mem_Ioo.mp hzd.1
      let h2 := Set.mem_Ioo.mp hzd.2
      let hre : z.re ∈ Set.Icc ((0 : ℂ).re) (((ρ : ℂ) + Complex.I * (ρ : ℂ)).re) :=
        Set.mem_Icc.mpr
          ⟨hz0re.symm.trans_le ((min_eq_left hzre).symm.trans_le (le_of_lt h1.1)),
            (le_of_lt h1.2).trans_eq ((max_eq_right hzre).trans hz1re)⟩
      let him : z.im ∈ Set.Icc ρ T :=
        Set.mem_Icc.mpr
          ⟨hz0im.symm.trans_le ((min_eq_left hzim).symm.trans_le (le_of_lt h2.1)),
            (le_of_lt h2.2).trans_eq ((max_eq_right hzim).trans hz1im)⟩
      hclosed (Complex.mem_reProdIm.mpr ⟨hre, him⟩)
  let hcauchy := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f z₀ z₁ Hc (hdiff.mono hsubD)
  let hIA := intervalIntegral_congr3
    (Eq.trans (left_upper_integrand f ρ).symm
      (congrArg (fun v : ℝ => fun x : ℝ => f ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I))
        (I_mul_ofReal_im ρ).symm))
    (I_mul_ofReal_re ρ).symm (ofReal_add_I_mul_re ρ T).symm
  let hIB := intervalIntegral_congr3
    (Eq.trans (left_upper_integrand f T).symm
      (congrArg (fun v : ℝ => fun x : ℝ => f ((x : ℂ) + ((v : ℝ) : ℂ) * Complex.I))
        (ofReal_add_I_mul_im ρ T).symm))
    (I_mul_ofReal_re ρ).symm (ofReal_add_I_mul_re ρ T).symm
  let hIC := intervalIntegral_congr3
    (Eq.trans (left_vert_integrand f ρ).symm
      (congrArg (fun v : ℝ => fun y : ℝ => f (((v : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        (ofReal_add_I_mul_re ρ T).symm))
    (I_mul_ofReal_im ρ).symm (ofReal_add_I_mul_im ρ T).symm
  let hID := intervalIntegral_congr3
    (Eq.trans (left_pv_integrand f).symm
      (congrArg (fun v : ℝ => fun y : ℝ => f (((v : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        (I_mul_ofReal_re ρ).symm))
    (I_mul_ofReal_im ρ).symm (ofReal_add_I_mul_im ρ T).symm
  Eq.trans
    (congrArg₂ (· - ·)
      (congrArg₂ (· + ·) (congrArg₂ (· - ·) hIA hIB) (congrArg (HMul.hMul Complex.I) hIC))
      (congrArg (HMul.hMul Complex.I) hID))
    hcauchy

/-- Transport the right-half deleted-disk model boundary to the left endpoint
half-collar coordinates. -/
theorem Complex.leftEndpointHalfRectangleDeletedDiskBoundary_of_model
    (f : ℂ → ℂ)
    {ρ : ℝ}
    (hmodel :
      (∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im + ρ : ℝ) : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ((0 : ℂ).im - ρ)..((0 : ℂ).im + ρ),
                f ((((0 : ℂ).re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((0 : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
          Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 :=
  hmodel

/-- The local Cauchy-Goursat deformation across the left endpoint
half-rectangle collar outside the deleted disk.

This is the precise topological core of the left endpoint principal-value
indentation.  The two horizontal chord integrals at heights `±ρ`, the middle
safe vertical segment, and the counterclockwise right semicircle bound the
right half-rectangle with the endpoint disk removed.  Since `f` is
holomorphic on the punctured endpoint cap, the oriented boundary integral of
this collar vanishes. -/
theorem Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
          Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 :=
  let hcont_model : ContinuousOn f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) :=
    hcont
  let hdiff_model : DifferentiableOn ℂ f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) :=
    hdiff
  let hmodel :=
    Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
      f (0 : ℂ) T ρ le_rfl hρ
      (Real.endpoint_radius_lt_abs_height hT hρT)
      hcont_model hdiff_model
  Complex.leftEndpointHalfRectangleDeletedDiskBoundary_of_model f hmodel

/-- The full safe vertical side in the left endpoint cap is the concatenation
of its lower, middle, and upper pieces. -/
theorem Complex.leftEndpointSafeVerticalIntegral_split_three
    (f : ℂ → ℂ)
    (T ρ : ℝ)
    (hlower :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) (-ρ))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-ρ) ρ)
    (hupper :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume ρ T) :
    ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
        (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
  let hleft := intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  let hleft_integrable := hlower.trans hmiddle
  let hright := intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  calc ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))
      = (∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := hright.symm
    _ = ((∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
      congrArg (fun left : ℂ => left + ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) hleft.symm
    _ = (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := rfl

/-- Collect the three oriented group integrals (two rectangular, one deleted
disk) into the single left endpoint cap/collar boundary expression, cancelling
the two interior chords and grouping the safe and principal-value terms. -/
theorem Complex.leftEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
        (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT + Complex.I * (safeLower + safeMiddle + safeUpper) -
        Complex.I * (pvLower + pvUpper) - arc :=
  let hgen :=
    add_collect_caps lowerT upperT (Complex.I * safeLower) (Complex.I * safeUpper)
      (Complex.I * safeMiddle) (Complex.I * pvLower) (Complex.I * pvUpper) arc
      lowerChord upperChord
  (Complex.boundaryGroupIPvTerms pvLower pvUpper) ▸
    (Complex.boundaryGroupISafeTerms safeLower safeMiddle safeUpper) ▸ hgen

/-- Complex-linear algebra assembling the two rectangular endpoint identities
and the deleted-disk collar identity into the full left endpoint cap/collar boundary
identity. -/
theorem Complex.leftEndpointCapCollarBoundary_algebra
    (lowerT upperT lowerChord upperChord safe safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ)
    (hsafe : safe = safeLower + safeMiddle + safeUpper)
    (hlower :
      lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower = 0)
    (hupper :
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper = 0)
    (hhalf :
      lowerChord - upperChord + Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * safe -
        Complex.I * (pvLower + pvUpper) - arc =
      0 :=
  let hsum : (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
      (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
        (lowerChord - upperChord + Complex.I * safeMiddle - arc) = 0 :=
    Eq.trans (congrArg₂ (· + ·) (congrArg₂ (· + ·) hlower hupper) hhalf)
      (Eq.trans (congrArg (· + (0 : ℂ)) (add_zero (0 : ℂ))) (add_zero (0 : ℂ)))
  let hcollected :=
    Complex.leftEndpointCapCollarBoundary_collect
      lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc
  let hzero : lowerT - upperT + Complex.I * (safeLower + safeMiddle + safeUpper) -
      Complex.I * (pvLower + pvUpper) - arc = 0 :=
    hcollected ▸ hsum
  hsafe.symm ▸ hzero

/-- Generic oriented boundary integral of a left endpoint cap/collar.

This is the local topological object behind the Abel-Plana endpoint at `0`.
The Abel-Plana rectangle integrand is only a later specialization of this
ordinary deleted-disk collar Cauchy-Goursat boundary. -/
noncomputable def Complex.leftEndpointCapCollarOrientedBoundaryIntegral
    (f : ℂ → ℂ)
    (T ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
        Complex.I * (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I *
            ((∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) +
              ∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic Cauchy-Goursat theorem for the left endpoint cap/collar.

This is the classical local deleted-disk collar contour theorem: if `f` is
continuous and holomorphic on the rectangular cap with the endpoint disk
deleted, the oriented boundary integral of that cap is zero. -/
theorem Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.leftEndpointCapCollarOrientedBoundaryIntegral f T ρ = 0 :=
  let g : ℝ → ℂ := fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ))
  let hsafe_integrable : ∀ a b : ℝ, a ≤ b →
        (∀ y ∈ [[a, b]], y ∈ [[-T, T]]) →
          IntervalIntegrable g volume a b := fun a b hab hinterval_subset =>
    let hpath_cont :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    let hpath_mem : ∀ y ∈ [[a, b]],
          ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := fun y hy =>
      Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar hρ (hinterval_subset y hy)
    let hcg : ContinuousOn g (Set.Icc a b) := hcont.comp hpath_cont hpath_mem
    let hcg_uIcc : ContinuousOn g (Set.uIcc a b) := (Set.uIcc_of_le hab).symm ▸ hcg
    hcg_uIcc.intervalIntegrable
  let hlower_interval :=
    Real.endpoint_lower_interval_subset_height hT hρ hρT
  let hmiddle_interval :=
    Real.endpoint_middle_interval_subset_height hρ hρT
  let hupper_interval :=
    Real.endpoint_upper_interval_subset_height hT hρ hρT
  let hsafe_split :=
    Complex.leftEndpointSafeVerticalIntegral_split_three
      f T ρ
      (hsafe_integrable (-T) (-ρ) (neg_le_neg hρT.le) hlower_interval)
      (hsafe_integrable (-ρ) ρ (neg_le_self hρ.le) hmiddle_interval)
      (hsafe_integrable ρ T hρT.le hupper_interval)
  let hlower_zero :=
    Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
      f T hT hρ hρT hcont hdiff
  let hupper_zero :=
    Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
      f T hρ hρT hcont hdiff
  let hhalf_zero :=
    Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
      f T hT hρ hρT hcont hdiff
  Complex.leftEndpointCapCollarBoundary_algebra
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ)))
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ)))
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ)))
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ)))
    (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
    (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ)))
    (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
    (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
    (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ)))
    (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ)))
    (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
    hsafe_split
    hlower_zero
    hupper_zero
    hhalf_zero

/-- Oriented unnormalized boundary expression of the left endpoint cap/collar.

The five terms are, in order: lower collar, upper collar with opposite
orientation, right safe-strip edge, principal-value left edge with opposite
orientation, and the endpoint semicircle with the punctured-domain orientation
moved to the left-hand side. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
      Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Unfolding of the left endpoint cap/collar oriented boundary into its
straight collar sides and right semicircular deleted-boundary side. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_unfold
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  rfl

/-- The Abel-Plana left endpoint oriented boundary is the generic left cap
boundary specialized to the logarithmic cotangent rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.leftEndpointCapCollarOrientedBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        T ρ :=
  rfl

/-- Solving the left endpoint oriented-boundary Cauchy equation gives the
left endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
  sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the local deleted-disk collar theorem for the endpoint pole at `0`:
the boundary of the right endpoint collar, after deleting the endpoint
semicircle, has zero integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
    {w : ℂ}
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
  calc Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
        Complex.leftEndpointCapCollarOrientedBoundaryIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          T ρ :=
      Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic w T ρ
    _ = 0 :=
      Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        T hT hρ
        (Real.endpoint_radius_lt_height_of_lt_abs_height_half hT hdeleted_geometry.2.1)
        hcont_left hdiff_left

end

end LFunctions
end Boundary
