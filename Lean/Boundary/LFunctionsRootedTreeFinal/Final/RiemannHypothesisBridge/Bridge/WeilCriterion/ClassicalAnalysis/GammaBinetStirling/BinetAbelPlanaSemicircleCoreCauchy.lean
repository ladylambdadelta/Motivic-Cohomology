import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleCoreBoundary

/-!
# Curvilinear semicircle core Cauchy-Goursat layer

This file owns the right and left deleted half-rectangle core boundary theorems
used by finite Abel-Plana cap-collar and punctured-boundary accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology Interval

/-- Ordered bounds give membership in the corresponding unordered interval. -/
theorem Real.mem_uIcc_of_ordered_bounds
    {a b x : ℝ}
    (hab : a ≤ b)
    (hleft : a ≤ x)
    (hright : x ≤ b) :
    x ∈ [[a, b]] :=
  Eq.subst
    (motive := fun s : Set ℝ => x ∈ s)
    (Eq.symm (Set.uIcc_of_le hab))
    (And.intro hleft hright)

/-- The lower endpoint of a radius-`ρ` vertical core lies in a taller
height interval whenever the ambient height dominates `ρ`. -/
theorem Complex.center_sub_radius_mem_height_uIcc
    (c : ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ_nonneg : 0 ≤ ρ)
    (hρT : ρ < |T|) :
    c.im - ρ ∈ [[c.im - T, c.im + T]] := by
  match lt_or_ge T 0 with
  | Or.inl hT_lt =>
    have hT_le : T ≤ 0 := le_of_lt hT_lt
    have hρ_lt_negT : ρ < -T := by
      have habs : |T| = -T := abs_of_neg hT_lt
      exact Eq.subst (motive := fun u : ℝ => ρ < u) habs hρT
    have hρ_le_negT : ρ ≤ -T := le_of_lt hρ_lt_negT
    have hT_le_negT : T ≤ -T := by
      exact le_trans hT_le (neg_nonneg.mpr hT_le)
    have hT_le_negρ : T ≤ -ρ := by
      have hraw : - -T ≤ -ρ :=
        neg_le_neg hρ_le_negT
      exact Eq.subst
        (motive := fun u : ℝ => u ≤ -ρ)
        (neg_neg T)
        hraw
    have horder : c.im + T ≤ c.im - T :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left hT_le_negT c.im
    have hleft : c.im + T ≤ c.im - ρ :=
      (sub_eq_add_neg c.im ρ) ▸
        add_le_add_left hT_le_negρ c.im
    have hright : c.im - ρ ≤ c.im - T :=
      (sub_eq_add_neg c.im ρ) ▸
        (sub_eq_add_neg c.im T) ▸
          add_le_add_left
            (le_trans (neg_nonpos.mpr hρ_nonneg) (neg_nonneg.mpr hT_le))
            c.im
    have hmem_reversed :
        c.im - ρ ∈ [[c.im + T, c.im - T]] :=
      Real.mem_uIcc_of_ordered_bounds horder hleft hright
    exact Eq.subst
      (motive := fun s : Set ℝ => c.im - ρ ∈ s)
      (Set.uIcc_comm (c.im + T) (c.im - T))
      hmem_reversed
  | Or.inr hT =>
    have hρ_lt_T : ρ < T := by
      have habs : |T| = T := abs_of_nonneg hT
      exact Eq.subst (motive := fun u : ℝ => ρ < u) habs hρT
    have hρ_le_T : ρ ≤ T := le_of_lt hρ_lt_T
    have horder : c.im - T ≤ c.im + T :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left (neg_le_self hT) c.im
    have hleft : c.im - T ≤ c.im - ρ :=
      (sub_eq_add_neg c.im T) ▸
        (sub_eq_add_neg c.im ρ) ▸
          add_le_add_left (neg_le_neg hρ_le_T) c.im
    have hright : c.im - ρ ≤ c.im + T :=
      (sub_eq_add_neg c.im ρ) ▸
        add_le_add_left (le_trans (neg_nonpos.mpr hρ_nonneg) hT) c.im
    exact Real.mem_uIcc_of_ordered_bounds horder hleft hright

/-- The upper endpoint of a radius-`ρ` vertical core lies in a taller
height interval whenever the ambient height dominates `ρ`. -/
theorem Complex.center_add_radius_mem_height_uIcc
    (c : ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ_nonneg : 0 ≤ ρ)
    (hρT : ρ < |T|) :
    c.im + ρ ∈ [[c.im - T, c.im + T]] := by
  match lt_or_ge T 0 with
  | Or.inl hT_lt =>
    have hT_le : T ≤ 0 := le_of_lt hT_lt
    have hρ_lt_negT : ρ < -T := by
      have habs : |T| = -T := abs_of_neg hT_lt
      exact Eq.subst (motive := fun u : ℝ => ρ < u) habs hρT
    have hρ_le_negT : ρ ≤ -T := le_of_lt hρ_lt_negT
    have hT_le_negT : T ≤ -T := by
      exact le_trans hT_le (neg_nonneg.mpr hT_le)
    have horder : c.im + T ≤ c.im - T :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left hT_le_negT c.im
    have hleft : c.im + T ≤ c.im + ρ :=
      add_le_add_left (le_trans hT_le hρ_nonneg) c.im
    have hright : c.im + ρ ≤ c.im - T :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left hρ_le_negT c.im
    have hmem_reversed :
        c.im + ρ ∈ [[c.im + T, c.im - T]] :=
      Real.mem_uIcc_of_ordered_bounds horder hleft hright
    exact Eq.subst
      (motive := fun s : Set ℝ => c.im + ρ ∈ s)
      (Set.uIcc_comm (c.im + T) (c.im - T))
      hmem_reversed
  | Or.inr hT =>
    have hρ_lt_T : ρ < T := by
      have habs : |T| = T := abs_of_nonneg hT
      exact Eq.subst (motive := fun u : ℝ => ρ < u) habs hρT
    have hρ_le_T : ρ ≤ T := le_of_lt hρ_lt_T
    have horder : c.im - T ≤ c.im + T :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left (neg_le_self hT) c.im
    have hleft : c.im - T ≤ c.im + ρ :=
      (sub_eq_add_neg c.im T) ▸
        add_le_add_left (le_trans (neg_nonpos.mpr hT) hρ_nonneg) c.im
    have hright : c.im + ρ ≤ c.im + T :=
      add_le_add_left hρ_le_T c.im
    exact Real.mem_uIcc_of_ordered_bounds horder hleft hright

/-- If the ambient height strictly dominates the deletion radius, the right core
collar lies in the corresponding taller right collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρ_nonneg : 0 ≤ ρ)
    (hρT : ρ < |T|) :
    Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ ⊆
      Complex.rightHalfRectangleDeletedDiskDomain c T a ρ := by
  intro z hz
  match hz with
  | ⟨⟨hre, him⟩, hnot_ball⟩ =>
    have him_left :
        c.im - ρ ∈ [[c.im - T, c.im + T]] := by
      exact Complex.center_sub_radius_mem_height_uIcc c T hρ_nonneg hρT
    have him_right :
        c.im + ρ ∈ [[c.im - T, c.im + T]] := by
      exact Complex.center_add_radius_mem_height_uIcc c T hρ_nonneg hρT
    have him_tall : z.im ∈ [[c.im - T, c.im + T]] :=
      Set.uIcc_subset_uIcc him_left him_right him
    exact ⟨⟨hre, him_tall⟩, hnot_ball⟩

/-- If the ambient height strictly dominates the deletion radius, the left core
collar lies in the corresponding taller left collar. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρ_nonneg : 0 ≤ ρ)
    (hρT : ρ < |T|) :
    Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ ⊆
      Complex.leftHalfRectangleDeletedDiskDomain c T a ρ := by
  intro z hz
  match hz with
  | ⟨⟨hre, him⟩, hnot_ball⟩ =>
    have him_left :
        c.im - ρ ∈ [[c.im - T, c.im + T]] := by
      exact Complex.center_sub_radius_mem_height_uIcc c T hρ_nonneg hρT
    have him_right :
        c.im + ρ ∈ [[c.im - T, c.im + T]] := by
      exact Complex.center_add_radius_mem_height_uIcc c T hρ_nonneg hρT
    have him_tall : z.im ∈ [[c.im - T, c.im + T]] :=
      Set.uIcc_subset_uIcc him_left him_right him
    exact ⟨⟨hre, him_tall⟩, hnot_ball⟩

/-- The inner right edge of the radius-`ρ` core lies on the larger right edge
interval of radius `a`. -/
theorem Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc
    (c : ℂ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    c.re + ρ ∈ [[c.re, c.re + a]] := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have horder : c.re ≤ c.re + a := le_add_of_nonneg_right ha
  have hleft : c.re ≤ c.re + ρ := le_add_of_nonneg_right hρ.le
  have hright : c.re + ρ ≤ c.re + a := add_le_add_left hρa c.re
  exact Real.mem_uIcc_of_ordered_bounds horder hleft hright

/-- The smaller core real interval is contained in the larger real interval. -/
theorem Complex.rightHalfCore_re_uIcc_subset_outerRe_uIcc
    (c : ℂ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    [[c.re, c.re + ρ]] ⊆ [[c.re, c.re + a]] := by
  intro x hx
  have hright_endpoint :
      c.re + ρ ∈ [[c.re, c.re + a]] :=
    Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ
  exact Set.uIcc_subset_uIcc Set.left_mem_uIcc hright_endpoint hx

/-- Curvilinear Cauchy-Goursat theorem for the right half-rectangle collar
outside a deleted disk.

This is the exact classical topological input: the two horizontal chords, the
safe vertical chord, and the right semicircle are the positively oriented
boundary of the right half-rectangle with the disk removed. -/
theorem Complex.rightHalfRectangleDeletedDiskCurvilinearCauchyGoursat
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  have hcore_subset :
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
    intro z hz
    match hz with
    | ⟨⟨hre, him⟩, hnot_ball⟩ =>
      have hre_big : z.re ∈ [[c.re, c.re + a]] :=
        Complex.rightHalfCore_re_uIcc_subset_outerRe_uIcc c hρa hρ hre
      exact ⟨⟨hre_big, him⟩, hnot_ball⟩
  have hcont_core :
      ContinuousOn f (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    hcont.mono hcore_subset
  have hdiff_core :
      DifferentiableOn ℂ f (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    hdiff.mono hcore_subset
  have hcore_zero :
      Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ = 0 :=
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundary_eq_zero
      f c hρ hcont_core hdiff_core
  have htail_zero :
      Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ = 0 :=
    Complex.rightHalfRectangleDeletedDiskCore_rectangularTailBoundary_eq_zero
      f c a hρa hρ hcont hdiff
  match
    Complex.rightHalfRectangleDeletedDiskCore_boundary_intervalIntegrable
      f c a hρa hρ hcont with
  | ⟨hbottom_full, htop_full, _hvertical_full, _harc_full⟩ =>
    have hinner_re :
        c.re + ρ ∈ [[c.re, c.re + a]] :=
      Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ
    have hbottom₁ :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          volume c.re (c.re + ρ) :=
      Complex.intervalIntegrable_of_mem_uIcc
        (F := fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (a := c.re) (b := c.re + a)
        (c := c.re) (d := c.re + ρ)
        hbottom_full Set.left_mem_uIcc hinner_re
    have hbottom₂ :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          volume (c.re + ρ) (c.re + a) :=
      Complex.intervalIntegrable_of_mem_uIcc
        (F := fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        (a := c.re) (b := c.re + a)
        (c := c.re + ρ) (d := c.re + a)
        hbottom_full hinner_re Set.right_mem_uIcc
    have htop₁ :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          volume c.re (c.re + ρ) :=
      Complex.intervalIntegrable_of_mem_uIcc
        (F := fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (a := c.re) (b := c.re + a)
        (c := c.re) (d := c.re + ρ)
        htop_full Set.left_mem_uIcc hinner_re
    have htop₂ :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          volume (c.re + ρ) (c.re + a) :=
      Complex.intervalIntegrable_of_mem_uIcc
        (F := fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        (a := c.re) (b := c.re + a)
        (c := c.re + ρ) (d := c.re + a)
        htop_full hinner_re Set.right_mem_uIcc
    calc
      Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
          Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ +
            Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ :=
        Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_semicircularCore_add_rectangularTail
          f c a ρ hρa hbottom₁ hbottom₂ htop₁ htop₂
      _ = 0 :=
        Eq.trans
          (congrArg₂ HAdd.hAdd hcore_zero htail_zero)
          (zero_add 0)

/-- Core Cauchy-Goursat theorem for the right half-rectangle collar outside a
deleted disk.

This wrapper keeps the local Abel-Plana naming stable while the owner theorem
above records the actual analytic input. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 :=
  Complex.rightHalfRectangleDeletedDiskCurvilinearCauchyGoursat
    f c a hρa hρ hcont hdiff

/-- Core Cauchy-Goursat theorem for the left half-rectangle collar outside a
deleted disk. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  have hcont_turn :
      ContinuousOn (Complex.halfTurnPullback c f)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :=
    Complex.continuousOn_halfTurnPullback_rightCore_of_leftCore
      f c a ρ (le_trans hρ.le hρa) hρ.le hcont
  have hdiff_turn :
      DifferentiableOn ℂ (Complex.halfTurnPullback c f)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :=
    Complex.differentiableOn_halfTurnPullback_rightCore_of_leftCore
      f c a ρ (le_trans hρ.le hρa) hρ.le hdiff
  calc
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
        -Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
          (Complex.halfTurnPullback c f) c a ρ :=
      Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_neg_halfTurn_right
        f c a ρ
    _ = 0 :=
      neg_eq_zero.mpr
        (Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
          (Complex.halfTurnPullback c f) c a hρa hρ hcont_turn hdiff_turn)

/-- Generic Cauchy-Goursat theorem for the right half-rectangle collar outside a
deleted disk.

This is the reusable local curvilinear contour theorem.  Its boundary is the
two lower/upper chord segments, the safe vertical chord at `c.re + a`, and the
counterclockwise right semicircle with deleted-boundary orientation subtracted. -/
theorem Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hρT : ρ < |T|)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskDomain c T a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskDomain c T a ρ)) :
    (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in c.re..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_core :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hcont.mono
      (Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρ.le hρT)
  have hdiff_core :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hdiff.mono
      (Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρ.le hρT)
  show
    (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in c.re..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0
  exact
    Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
      f c a hρa hρ hcont_core hdiff_core

/-- Generic Cauchy-Goursat theorem for the left half-rectangle collar outside a
deleted disk.

This is the reflected local curvilinear contour theorem.  Its boundary is the
two lower/upper chord segments, the safe vertical chord at `c.re - a`, and the
counterclockwise left semicircle with deleted-boundary orientation subtracted. -/
theorem Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hρT : ρ < |T|)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskDomain c T a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskDomain c T a ρ)) :
    (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in (c.re - a)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_core :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hcont.mono
      (Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρ.le hρT)
  have hdiff_core :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hdiff.mono
      (Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρ.le hρT)
  show
    (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in (c.re - a)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0
  exact
    Complex.leftHalfRectangleDeletedDiskCoreBoundary_eq_zero
      f c a hρa hρ hcont_core hdiff_core

end

end LFunctions
end Boundary
