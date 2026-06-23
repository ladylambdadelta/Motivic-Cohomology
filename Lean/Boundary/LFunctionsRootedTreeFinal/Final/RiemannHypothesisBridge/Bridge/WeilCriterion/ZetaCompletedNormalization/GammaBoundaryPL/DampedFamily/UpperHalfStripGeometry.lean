import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.UpperTailAbsorbers

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- The compact central rectangle of a vertical strip. -/
def verticalStripCompactHeightRectangle
    (a b : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ ‖z.im‖ ≤ 1}

/-- The bounded-height rectangle of a vertical strip, with variable height. -/
def verticalStripBoundedHeightRectangle
    (a b R : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ ‖z.im‖ ≤ R}

/-- The closed upper half-strip starting at height `1`. -/
def verticalStripUpperHalfStrip
    (a b : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ z.im}

/-- The finite upper half-strip rectangle between heights `1` and `R`. -/
def verticalStripUpperHalfStripRectangle
    (a b R : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ z.im ∧ z.im ≤ R}

/-- The bottom edge of the shifted upper half-strip rectangle. -/
def verticalStripUpperHalfStripBottomEdge
    (a b : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ z.im = 1}

/-- The two vertical boundary rays of the shifted upper half-strip. -/
def verticalStripUpperHalfStripVerticalBoundary
    (a b : ℝ) : Set ℂ :=
  {z : ℂ | (z.re = a ∨ z.re = b) ∧ 1 ≤ z.im}

/-- The finite shifted upper half-strip rectangle boundary: bottom edge, top
edge, and the two vertical sides. -/
def verticalStripUpperHalfStripRectangleBoundary
    (a b R : ℝ) : Set ℂ :=
  {z : ℂ |
    a ≤ z.re ∧ z.re ≤ b ∧ 1 ≤ z.im ∧ z.im ≤ R ∧
      (z.im = 1 ∨ z.im = R ∨ z.re = a ∨ z.re = b)}

/-- The bottom edge of the shifted upper half-strip lies in the compact-height
rectangle. -/
theorem verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle
    {a b : ℝ} :
    verticalStripUpperHalfStripBottomEdge a b ⊆
      verticalStripCompactHeightRectangle a b := by
  intro z hz
  have him_norm : ‖z.im‖ = 1 := by
    calc
      ‖z.im‖ = ‖(1 : ℝ)‖ := by
        exact congrArg (fun y : ℝ => ‖y‖) hz.2.2
      _ = 1 := norm_one
  exact
    ⟨hz.1, hz.2.1,
      Eq.subst
        (motive := fun x : ℝ => x ≤ 1)
        him_norm.symm
        (le_of_eq rfl)⟩

/-- Finite upper-rectangle maximum-modulus principle from a frontier bound.

This is the compact rectangle core of the shifted upper half-strip argument.
The later half-strip theorem supplies the frontier bound from the bottom edge,
the two vertical sides, and the top-edge damping estimate. -/
theorem verticalStripUpperHalfStripRectangle_norm_le_of_frontier_bound
    (g : ℂ → ℂ)
    (a b R C : ℝ)
    (hab : a < b)
    (hR : 1 < R)
    (hhol :
      DiffContOnCl ℂ g (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R))
    (hfrontier :
      ∀ z : ℂ,
        z ∈ frontier (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) →
        ‖g z‖ ≤ C) :
    ∀ z : ℂ,
      z ∈ closure (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) →
      ‖g z‖ ≤ C := by
  exact
    fun z hz =>
      Complex.norm_le_of_forall_mem_frontier_norm_le
        ((isBounded_Ioo a b).reProdIm (isBounded_Ioo (1 : ℝ) R))
        hhol
        hfrontier
        hz

/-- Closed upper half-strip rectangle points lie in the closure of the
corresponding open rectangle. -/
theorem verticalStripUpperHalfStripRectangle_mem_closure_openRectangle
    {a b R : ℝ}
    (hab : a < b)
    (hR : 1 < R)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b)
    (hz1 : 1 ≤ z.im)
    (hzR : z.im ≤ R) :
    z ∈ closure (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) := by
  have hz_closed :
      z ∈ Set.Icc a b ×ℂ Set.Icc (1 : ℝ) R :=
    ⟨⟨hza, hzb⟩, ⟨hz1, hzR⟩⟩
  have hclosure_eq :
      closure (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) =
        Set.Icc a b ×ℂ Set.Icc (1 : ℝ) R := by
    calc
      closure (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) =
          closure (Set.Ioo a b) ×ℂ closure (Set.Ioo (1 : ℝ) R) :=
        closure_reProdIm (Set.Ioo a b) (Set.Ioo (1 : ℝ) R)
      _ = Set.Icc a b ×ℂ closure (Set.Ioo (1 : ℝ) R) := by
        exact congrArg
          (fun S : Set ℝ => S ×ℂ closure (Set.Ioo (1 : ℝ) R))
          (closure_Ioo hab.ne)
      _ = Set.Icc a b ×ℂ Set.Icc (1 : ℝ) R := by
        exact congrArg
          (fun S : Set ℝ => Set.Icc a b ×ℂ S)
          (closure_Ioo hR.ne)
  exact
    Eq.subst
      (motive := fun S : Set ℂ => z ∈ S)
      hclosure_eq.symm
      hz_closed

/-- Strip holomorphy restricts to each finite shifted upper half-strip
rectangle. -/
theorem diffContOnCl_upperHalfStripRectangle_of_verticalStrip
    (g : ℂ → ℂ)
    {a b R : ℝ}
    (hhol : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b)) :
    DiffContOnCl ℂ g (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) := by
  exact
    hhol.mono
      (fun z hz => hz.1)

/-- The frontier of the finite shifted upper half-strip open rectangle lies in
the explicit rectangle boundary. -/
theorem verticalStripUpperHalfStripRectangle_frontier_subset_boundary
    {a b R : ℝ}
    (hab : a < b)
    (hR : 1 < R) :
    frontier (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) ⊆
      verticalStripUpperHalfStripRectangleBoundary a b R := by
  intro z hz
  have hfrontier_eq :
      frontier (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) =
        closure (Set.Ioo a b) ×ℂ frontier (Set.Ioo (1 : ℝ) R) ∪
          frontier (Set.Ioo a b) ×ℂ closure (Set.Ioo (1 : ℝ) R) :=
    frontier_reProdIm (Set.Ioo a b) (Set.Ioo (1 : ℝ) R)
  have hz_union :
      z ∈ closure (Set.Ioo a b) ×ℂ frontier (Set.Ioo (1 : ℝ) R) ∪
          frontier (Set.Ioo a b) ×ℂ closure (Set.Ioo (1 : ℝ) R) :=
    Eq.subst
      (motive := fun S : Set ℂ => z ∈ S)
      hfrontier_eq
      hz
  match hz_union with
  | Or.inl hz_horizontal =>
      have hre_icc : z.re ∈ Set.Icc a b :=
        Eq.subst
          (motive := fun S : Set ℝ => z.re ∈ S)
          (closure_Ioo hab.ne)
          hz_horizontal.1
      have him_frontier : z.im ∈ ({(1 : ℝ), R} : Set ℝ) :=
        Eq.subst
          (motive := fun S : Set ℝ => z.im ∈ S)
          (frontier_Ioo hR)
          hz_horizontal.2
      match Set.mem_insert_iff.mp him_frontier with
      | Or.inl him_bottom =>
          exact
            ⟨hre_icc.1, hre_icc.2,
              le_of_eq him_bottom.symm,
              le_trans (le_of_lt hR) (le_of_eq him_bottom),
              Or.inl him_bottom⟩
      | Or.inr him_top_singleton =>
          have him_top : z.im = R :=
            Set.mem_singleton_iff.mp him_top_singleton
          exact
            ⟨hre_icc.1, hre_icc.2,
              le_trans (le_of_lt hR) (le_of_eq him_top.symm),
              le_of_eq him_top,
              Or.inr (Or.inl him_top)⟩
  | Or.inr hz_vertical =>
      have hre_frontier : z.re ∈ ({a, b} : Set ℝ) :=
        Eq.subst
          (motive := fun S : Set ℝ => z.re ∈ S)
          (frontier_Ioo hab)
          hz_vertical.1
      have him_icc : z.im ∈ Set.Icc (1 : ℝ) R :=
        Eq.subst
          (motive := fun S : Set ℝ => z.im ∈ S)
          (closure_Ioo hR.ne)
          hz_vertical.2
      match Set.mem_insert_iff.mp hre_frontier with
      | Or.inl hre_left =>
          exact
            ⟨le_of_eq hre_left.symm,
              le_trans (le_of_eq hre_left) (le_of_lt hab),
              him_icc.1, him_icc.2,
              Or.inr (Or.inr (Or.inl hre_left))⟩
      | Or.inr hre_right_singleton =>
          have hre_right : z.re = b :=
            Set.mem_singleton_iff.mp hre_right_singleton
          exact
            ⟨le_trans (le_of_lt hab) (le_of_eq hre_right.symm),
              le_of_eq hre_right,
              him_icc.1, him_icc.2,
              Or.inr (Or.inr (Or.inr hre_right))⟩

/-- Finite shifted upper half-strip rectangle maximum principle from explicit
bottom, top, and vertical-side bounds. -/
theorem verticalStripUpperHalfStripRectangle_norm_le_of_boundary
    (g : ℂ → ℂ)
    {a b R C : ℝ}
    (hab : a < b)
    (hR : 1 < R)
    (hhol : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b))
    (hbottom :
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖g z‖ ≤ C)
    (htop :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        z.im = R →
        ‖g z‖ ≤ C)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        z.im ≤ R →
        ‖g z‖ ≤ C)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        z.im ≤ R →
        ‖g z‖ ≤ C) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      1 ≤ z.im →
      z.im ≤ R →
      ‖g z‖ ≤ C := by
  have hrect_hol :
      DiffContOnCl ℂ g (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) :=
    diffContOnCl_upperHalfStripRectangle_of_verticalStrip g hhol
  have hfrontier :
      ∀ z : ℂ,
        z ∈ frontier (Set.Ioo a b ×ℂ Set.Ioo (1 : ℝ) R) →
        ‖g z‖ ≤ C :=
    fun z hz =>
      have hboundary :
          z ∈ verticalStripUpperHalfStripRectangleBoundary a b R :=
        verticalStripUpperHalfStripRectangle_frontier_subset_boundary hab hR hz
      match hboundary.2.2.2.2 with
      | Or.inl him_bottom =>
          hbottom z ⟨hboundary.1, hboundary.2.1, him_bottom⟩
      | Or.inr hnot_bottom =>
          match hnot_bottom with
          | Or.inl him_top =>
              htop z hboundary.1 hboundary.2.1 him_top
          | Or.inr hver =>
              match hver with
              | Or.inl hre_left =>
                  hleft z hre_left hboundary.2.2.1 hboundary.2.2.2.1
              | Or.inr hre_right =>
                  hright z hre_right hboundary.2.2.1 hboundary.2.2.2.1
  exact
    fun z hza hzb hz1 hzR =>
      verticalStripUpperHalfStripRectangle_norm_le_of_frontier_bound
        g a b R C hab hR hrect_hol hfrontier z
        (verticalStripUpperHalfStripRectangle_mem_closure_openRectangle
          hab hR hza hzb hz1 hzR)

/-- Exhaust the shifted upper half-strip by finite rectangles once the top
edges are eventually bounded by the same constant. -/
theorem verticalStripUpperHalfStrip_norm_le_of_eventual_top_boundary
    (g : ℂ → ℂ)
    {a b C : ℝ}
    (hab : a < b)
    (hhol : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b))
    (hbottom :
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖g z‖ ≤ C)
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖g z‖ ≤ C)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖g z‖ ≤ C)
    (htop :
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im = R →
          ‖g z‖ ≤ C) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      1 ≤ z.im →
      ‖g z‖ ≤ C := by
  match eventually_atTop.1 htop with
  | ⟨R0, hR0⟩ =>
      exact
        fun z hza hzb hz1 =>
          let R : ℝ := max (max R0 (z.im + 1)) 2
          have hR_ge_R0 : R0 ≤ R :=
            le_trans
              (le_max_left R0 (z.im + 1))
              (le_max_left (max R0 (z.im + 1)) 2)
          have hR_gt_one : 1 < R :=
            lt_of_lt_of_le
              (show (1 : ℝ) < 2 from one_lt_two)
              (le_max_right (max R0 (z.im + 1)) 2)
          have hz_le_R : z.im ≤ R :=
            have hz_le_add : z.im ≤ z.im + 1 :=
              le_add_of_nonneg_right zero_le_one
            le_trans
              (le_trans hz_le_add (le_max_right R0 (z.im + 1)))
              (le_max_left (max R0 (z.im + 1)) 2)
          have htop_R :
              ∀ w : ℂ,
                a ≤ w.re →
                w.re ≤ b →
                w.im = R →
                ‖g w‖ ≤ C :=
            hR0 R hR_ge_R0
          have hleft_R :
              ∀ w : ℂ,
                w.re = a →
                1 ≤ w.im →
                w.im ≤ R →
                ‖g w‖ ≤ C :=
            fun w hw_re hw_im _hw_R =>
              hleft w hw_re hw_im
          have hright_R :
              ∀ w : ℂ,
                w.re = b →
                1 ≤ w.im →
                w.im ≤ R →
                ‖g w‖ ≤ C :=
            fun w hw_re hw_im _hw_R =>
              hright w hw_re hw_im
          verticalStripUpperHalfStripRectangle_norm_le_of_boundary
            g hab hR_gt_one hhol hbottom htop_R hleft_R hright_R
            z hza hzb hz1 hz_le_R

/-- A subcritical open-strip Big-O estimate gives eventual horizontal top-edge
control on the open part of the strip.

This is only the filter extraction from the open-strip finite-order hypothesis:
the closed top-edge endpoints must still be supplied by the vertical boundary
rays. -/
theorem verticalStrip_finiteOrder_isBigO_eventually_topEdge_open_bound
    (f : ℂ → ℂ)
    {a b c D : ℝ}
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ K : ℝ,
      0 < K ∧
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a < z.re →
          z.re < b →
          z.im = R →
          ‖f z‖ ≤ K * Real.exp (D * Real.exp (c * R)) := by
  let strip : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  let heightFilter : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  match hD.exists_pos with
  | ⟨K, hK_pos, hK⟩ =>
      have hbound :
          ∀ᶠ z in heightFilter ⊓ 𝓟 strip,
            ‖f z‖ ≤
              K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ :=
        hK.bound
      have hheight_bound :
          ∀ᶠ z in heightFilter,
            z ∈ strip →
              ‖f z‖ ≤
                K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ :=
        (Filter.eventually_inf_principal).1 hbound
      have htop_raw :
          ∀ᶠ R : ℝ in Filter.atTop,
            ∀ z : ℂ,
              (_root_.abs ∘ Complex.im) z = R →
              z ∈ strip →
                ‖f z‖ ≤
                  K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ :=
        Filter.eventually_comap.mp hheight_bound
      have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 0 ≤ R :=
        eventually_ge_atTop (0 : ℝ)
      exact
        ⟨K, hK_pos,
          (htop_raw.and hlarge).mono
            fun R hR z hza hzb hz_im =>
              have hstrip : z ∈ strip :=
                ⟨hza, hzb⟩
              have hraw :
                  ‖f z‖ ≤
                    K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ :=
                hR.1 z
                  (show (_root_.abs ∘ Complex.im) z = R from
                    calc
                      (_root_.abs ∘ Complex.im) z = |z.im| := rfl
                      _ = |R| := congrArg _root_.abs hz_im
                      _ = R := abs_of_nonneg hR.2)
                  hstrip
              have hnorm_eq :
                  ‖Real.exp (D * Real.exp (c * |z.im|))‖ =
                    Real.exp (D * Real.exp (c * |z.im|)) :=
                Real.norm_of_nonneg
                  (le_of_lt
                    (Real.exp_pos (D * Real.exp (c * |z.im|))))
              have him_abs :
                  |z.im| = R := by
                calc
                  |z.im| = |R| := congrArg _root_.abs hz_im
                  _ = R := abs_of_nonneg hR.2
              have hexp_eq :
                  Real.exp (D * Real.exp (c * |z.im|)) =
                    Real.exp (D * Real.exp (c * R)) :=
                congrArg
                  (fun y : ℝ => Real.exp (D * Real.exp (c * y)))
                  him_abs
              have hrhs_eq :
                  K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ =
                    K * Real.exp (D * Real.exp (c * R)) :=
                calc
                  K * ‖Real.exp (D * Real.exp (c * |z.im|))‖ =
                      K * Real.exp (D * Real.exp (c * |z.im|)) :=
                    congrArg (fun x : ℝ => K * x) hnorm_eq
                  _ = K * Real.exp (D * Real.exp (c * R)) :=
                    congrArg (fun x : ℝ => K * x) hexp_eq
              Eq.subst
                (motive := fun x : ℝ => ‖f z‖ ≤ x)
                hrhs_eq
                hraw⟩

/-- Horizontal top-edge eventual bound for the subcritical cosine-damped
family on the open part of the strip. -/
theorem verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_open_bound
    (f : ℂ → ℂ)
    {a b c d D ε : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a < z.re →
          z.re < b →
          z.im = R →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match
    verticalStrip_finiteOrder_isBigO_eventually_topEdge_open_bound
      f hD
  with
  | ⟨K, hK_pos, htop_f⟩ =>
      let L : ℝ := Real.cos (d * ((b - a) / 2)) / 2
      have hL_pos : 0 < L :=
        verticalStripSubcriticalCosineBarrierKernel_rightBoundary_halfCos_pos
          hab hd_pos hd_threshold
      have habsorb :
          ∀ᶠ R : ℝ in Filter.atTop,
            K * Real.exp (D * Real.exp (c * R)) *
                Real.exp (-(ε * L * Real.exp (d * R))) ≤ K :=
        doubleExponential_exp_mul_subcritical_absorber_eventually_le_const
          hK_pos hL_pos hε_pos hcd
      exact
        ⟨K, hK_pos,
          (htop_f.and habsorb).mono
            fun R hR z hza hzb hz_im =>
              have hf :
                  ‖f z‖ ≤ K * Real.exp (D * Real.exp (c * z.im)) := by
                have hraw :
                    ‖f z‖ ≤ K * Real.exp (D * Real.exp (c * R)) :=
                  hR.1 z hza hzb hz_im
                have hrhs :
                    K * Real.exp (D * Real.exp (c * R)) =
                      K * Real.exp (D * Real.exp (c * z.im)) :=
                  congrArg
                    (fun y : ℝ => K * Real.exp (D * Real.exp (c * y)))
                    hz_im.symm
                Eq.subst
                  (motive := fun x : ℝ => ‖f z‖ ≤ x)
                  hrhs
                  hraw
              have hpre :
                  ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
                    (K * Real.exp (D * Real.exp (c * z.im))) *
                      Real.exp
                        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                          Real.exp (d * z.im))) :=
                verticalStripSubcriticalCosineDampedFamily_topEdge_preAbsorption
                  f hab hd_pos hd_threshold (le_of_lt hε_pos)
                  (le_of_lt hza) (le_of_lt hzb) hf
              have htarget :
                  (K * Real.exp (D * Real.exp (c * z.im))) *
                      Real.exp
                        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                          Real.exp (d * z.im))) =
                    K * Real.exp (D * Real.exp (c * R)) *
                      Real.exp (-(ε * L * Real.exp (d * R))) := by
                calc
                  (K * Real.exp (D * Real.exp (c * z.im))) *
                      Real.exp
                        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                          Real.exp (d * z.im))) =
                    K * Real.exp (D * Real.exp (c * R)) *
                      Real.exp
                        (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                          Real.exp (d * R))) := by
                      exact congrArg₂
                        (fun x y : ℝ =>
                          K * Real.exp (D * Real.exp (c * x)) *
                            Real.exp
                              (-(ε * (Real.cos (d * ((b - a) / 2)) / 2) *
                                Real.exp (d * y))))
                        hz_im hz_im
                  _ =
                    K * Real.exp (D * Real.exp (c * R)) *
                      Real.exp (-(ε * L * Real.exp (d * R))) := rfl
              le_trans hpre
                (Eq.subst
                  (motive := fun x : ℝ => x ≤ K)
                  htarget.symm
                  hR.2)⟩

/-- Horizontal top-edge eventual finite-order envelope for the subcritical
cosine-damped family.  The envelope constants are assembled from the fixed
vertical-boundary envelope and the open-strip top absorber, so they are suitable
for later uniformization in `ε`. -/
theorem verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_finiteEnvelope
    (f : ℂ → ℂ)
    {a b c d D ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hA : 0 < A)
    (hB : 0 < B)
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A' : ℝ, ∃ B' : ℝ, ∃ m' : ℕ,
      0 < A' ∧
      0 < B' ∧
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im = R →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
            A' * Real.exp (B' * (1 + ‖z‖) ^ m') := by
  match
    verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_open_bound
      f hab hd_pos hd_threshold hε_pos hcd hD
  with
  | ⟨K, hK_pos, hopen⟩ =>
      let A' : ℝ := A + K
      let B' : ℝ := B + 1
      let m' : ℕ := m + 1
      have hA'_pos : 0 < A' := add_pos hA hK_pos
      have hB'_pos : 0 < B' := add_pos hB zero_lt_one
      have hK_le_A' : K ≤ A' :=
        le_add_of_nonneg_left (le_of_lt hA)
      have hA_le_A' : A ≤ A' :=
        le_add_of_nonneg_right (le_of_lt hK_pos)
      have hB_le_B' : B ≤ B' :=
        le_add_of_nonneg_right zero_le_one
      have hm_le_m' : m ≤ m' :=
        Nat.le_add_right m 1
      have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R :=
        eventually_ge_atTop (1 : ℝ)
      exact
        ⟨A', B', m', hA'_pos, hB'_pos,
          (hopen.and hlarge).mono
            fun R hR z hza hzb hz_im =>
              have hzim_ge : 1 ≤ z.im :=
                Eq.subst
                  (motive := fun y : ℝ => 1 ≤ y)
                  hz_im.symm
                  hR.2
              have hboundary_le :
                  A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
                    A' * Real.exp (B' * (1 + ‖z‖) ^ m') :=
                exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                  (le_of_lt hA)
                  hA_le_A'
                  hB_le_B'
                  (le_of_lt hB)
                  hm_le_m'
              have hopen_le :
                  K ≤ A' * Real.exp (B' * (1 + ‖z‖) ^ m') := by
                have hexp_one :
                    (1 : ℝ) ≤ Real.exp (B' * (1 + ‖z‖) ^ m') :=
                  Real.one_le_exp
                    (mul_nonneg
                      (le_of_lt hB'_pos)
                      (pow_nonneg
                        (add_nonneg zero_le_one (norm_nonneg z))
                        m'))
                calc
                  K ≤ A' := hK_le_A'
                  _ = A' * 1 := (mul_one A').symm
                  _ ≤ A' * Real.exp (B' * (1 + ‖z‖) ^ m') :=
                    mul_le_mul_of_nonneg_left hexp_one (le_of_lt hA'_pos)
              match lt_or_eq_of_le hza with
              | Or.inl hza_lt =>
                  match lt_or_eq_of_le hzb with
                  | Or.inl hzb_lt =>
                      le_trans (hR.1 z hza_lt hzb_lt hz_im) hopen_le
                  | Or.inr hzb_eq =>
                      le_trans
                        (hright z hzb_eq.symm hzim_ge)
                        hboundary_le
              | Or.inr hza_eq =>
                  le_trans
                    (hleft z hza_eq.symm hzim_ge)
                    hboundary_le⟩

/-- Horizontal top-edge eventual bound for the subcritical cosine-damped family
on the closed strip; endpoint points are supplied by the vertical boundary
package. -/
theorem verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_bound
    (f : ℂ → ℂ)
    {a b c d D ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))



    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
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
      ∀ᶠ R : ℝ in Filter.atTop,
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          z.im = R →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match
    verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_open_bound
      f hab hd_pos hd_threshold hε_pos hcd hD,
    verticalStripSubcriticalCosineDampedFamily_tail_boundary_package
      f hab hd_pos hd_threshold hε_pos hA hB hhol hleft hright
  with
  | ⟨Copen, hCopen_pos, hopen⟩,
    ⟨Cbd, hCbd_pos, hleft_bd, hright_bd⟩ =>
      let C : ℝ := max Copen Cbd
      have hC_pos : 0 < C :=
        lt_of_lt_of_le hCopen_pos (le_max_left Copen Cbd)
      have hCopen_le : Copen ≤ C :=
        le_max_left Copen Cbd
      have hCbd_le : Cbd ≤ C :=
        le_max_right Copen Cbd
      have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R :=
        eventually_ge_atTop (1 : ℝ)
      exact
        ⟨C, hC_pos,
          (hopen.and hlarge).mono
            fun R hR z hza hzb hz_im =>
              have hz_tail : 1 ≤ ‖z.im‖ := by
                have hzim_ge : 1 ≤ z.im :=
                  Eq.subst
                    (motive := fun y : ℝ => 1 ≤ y)
                    hz_im.symm
                    hR.2
                have hzim_nonneg : 0 ≤ z.im :=
                  le_trans zero_le_one hzim_ge
                have hnorm : ‖z.im‖ = z.im :=
                  Real.norm_of_nonneg hzim_nonneg
                Eq.subst
                  (motive := fun y : ℝ => 1 ≤ y)
                  hnorm.symm
                  hzim_ge
              match lt_or_eq_of_le hza with
              | Or.inl hza_strict =>
                  match lt_or_eq_of_le hzb with
                  | Or.inl hzb_strict =>
                      le_trans
                        (hR.1 z hza_strict hzb_strict hz_im)
                        hCopen_le
                  | Or.inr hzb_eq =>
                      le_trans
                        (hright_bd z hzb_eq.symm hz_tail)
                        hCbd_le
              | Or.inr hza_eq =>
                  le_trans
                    (hleft_bd z hza_eq.symm hz_tail)
                    hCbd_le⟩


end
end LFunctions
end Boundary
