import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.KernelZeroOrder.Owner

/-!
# Paley-Wiener horizontal twist

This file owns the horizontal-twist source, parameter rectangle, vertical-line
derivative compatibility, and compact rectangle seminorm bounds used before the
vertical integration-by-parts layer. It is copy-first extracted from the current
Paley-Wiener owner file and is not imported by that parent yet, so declaration
names intentionally match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The source on the vertical line `re z = x` after absorbing the horizontal exponential
factor into the compactly supported source. -/
noncomputable def zetaPaleyWienerHorizontalTwist
    (f : ZetaAdmissibleFunction) (x t : ℝ) : ℂ :=
  f.toZetaTestFunction' t * (Real.exp (x * t) : ℂ)

/-- The horizontal twist is smooth in the physical variable. -/
theorem zetaPaleyWienerHorizontalTwist_contDiff
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  have hsource :
      ContDiff ℝ ∞ (fun t : ℝ => f.toZetaTestFunction' t) := by
    exact f.smooth
  have hlinear :
      ContDiff ℝ ∞ (fun t : ℝ => x * t) :=
    contDiff_const.mul contDiff_id
  have hexp_real :
      ContDiff ℝ ∞ (fun t : ℝ => Real.exp (x * t)) :=
    Real.contDiff_exp.comp hlinear
  have hexp_complex :
      ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (x * t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp_real
  unfold zetaPaleyWienerHorizontalTwist
  exact hsource.mul hexp_complex

/-- The horizontal twist has compact support because the admissible source has compact
support. -/
theorem zetaPaleyWienerHorizontalTwist_hasCompactSupport
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  unfold zetaPaleyWienerHorizontalTwist
  exact f.toZetaTestFunction.hasCompactSupport.mul_right

/-- The horizontal twist is continuous in the physical variable. -/
theorem zetaPaleyWienerHorizontalTwist_continuous
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    Continuous (fun t : ℝ => zetaPaleyWienerHorizontalTwist f x t) := by
  exact (zetaPaleyWienerHorizontalTwist_contDiff f x).continuous

/-- The compact parameter-support rectangle used for uniform Paley-Wiener seminorms. -/
def zetaPaleyWienerParameterSupportRectangle
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc a b ×ˢ Set.Icc I.lower I.upper

/-- Membership in the Paley-Wiener parameter-support rectangle is exactly the four endpoint
inequalities. -/
theorem zetaPaleyWienerParameterSupportRectangle_mem
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) (p : ℝ × ℝ) :
    p ∈ zetaPaleyWienerParameterSupportRectangle I a b ↔
      a ≤ p.1 ∧ p.1 ≤ b ∧ I.lower ≤ p.2 ∧ p.2 ≤ I.upper := by
  constructor
  · intro hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  · intro hp
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩

/-- The parameter-support rectangle is compact. -/
theorem zetaPaleyWienerParameterSupportRectangle_isCompact
    (I : ZetaPaleyWienerSupportInterval f) (a b : ℝ) :
    IsCompact (zetaPaleyWienerParameterSupportRectangle I a b) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- The two-variable horizontal twist whose vertical-direction jets encode the repeated
integration-by-parts sources. -/
noncomputable def zetaPaleyWienerHorizontalTwistParameter
    (f : ZetaAdmissibleFunction) (p : ℝ × ℝ) : ℂ :=
  zetaPaleyWienerHorizontalTwist f p.1 p.2

/-- The vertical affine line through horizontal coordinate `x` in the parameter plane. -/
def zetaPaleyWienerVerticalLineEmbedding (x : ℝ) (t : ℝ) : ℝ × ℝ :=
  (x, t)

/-- The vertical affine line through `x` is smooth as a map from the physical line to the
parameter plane. -/
theorem zetaPaleyWienerVerticalLineEmbedding_contDiff
    (x : ℝ) :
    ContDiff ℝ ∞ (zetaPaleyWienerVerticalLineEmbedding x) := by
  unfold zetaPaleyWienerVerticalLineEmbedding
  exact contDiff_const.prod contDiff_id

/-- The parameter twist restricted to the vertical line through `x` is the horizontal twist. -/
theorem zetaPaleyWienerHorizontalTwistParameter_verticalLine
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistParameter f
        (zetaPaleyWienerVerticalLineEmbedding x t) =
      zetaPaleyWienerHorizontalTwist f x t := by
  rfl

/-- The vertical tangent direction in the `(x,t)` parameter plane. -/
def zetaPaleyWienerVerticalParameterDirection : ℝ × ℝ :=
  (0, 1)

/-- The linear part of the vertical affine line in the parameter plane. -/
def zetaPaleyWienerVerticalLinearEmbedding : ℝ →L[ℝ] ℝ × ℝ :=
  (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)

/-- The vertical linear embedding sends the scalar tangent `1` to the vertical direction. -/
theorem zetaPaleyWienerVerticalLinearEmbedding_one :
    zetaPaleyWienerVerticalLinearEmbedding 1 =
      zetaPaleyWienerVerticalParameterDirection := by
  rfl

/-- The vertical affine line is a translation of its linear vertical embedding. -/
theorem zetaPaleyWienerVerticalLineEmbedding_eq_translate_linear
    (x t : ℝ) :
    zetaPaleyWienerVerticalLineEmbedding x t =
      (x, 0) + zetaPaleyWienerVerticalLinearEmbedding t := by
  rfl

/-- The generic vertical-line compatibility theorem at derivative order zero. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_zero
    (F : ℝ × ℝ → ℂ) (x t : ℝ) :
    iteratedDeriv 0 (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ 0 F (x, t) :
          (Fin 0 → ℝ × ℝ) → ℂ)
        (fun _ : Fin 0 => zetaPaleyWienerVerticalParameterDirection) := by
  exact Eq.trans
    (congrFun (iteratedDeriv_zero (f := fun u : ℝ => F (x, u))) t)
    (iteratedFDeriv_zero_apply
      (f := F)
      (x := (x, t))
      (m := fun _ : Fin 0 => zetaPaleyWienerVerticalParameterDirection)).symm

/-- Frechet derivatives of the vertical affine restriction are obtained by precomposing the
ambient Frechet derivative with the vertical linear embedding. -/
theorem iteratedFDeriv_verticalLine_eq_comp_verticalLinearEmbedding
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
        (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding) := by
  let A : ℝ × ℝ := (x, 0)
  let L : ℝ →L[ℝ] ℝ × ℝ := zetaPaleyWienerVerticalLinearEmbedding
  let G : ℝ × ℝ → ℂ := fun p : ℝ × ℝ => F (A + p)
  have hline :
      (fun u : ℝ => F (x, u)) = G ∘ L := by
    funext u
    exact congrArg F (zetaPaleyWienerVerticalLineEmbedding_eq_translate_linear x u)
  have hG :
      ContDiff ℝ ∞ G := by
    exact hF.comp (contDiff_const.add L.contDiff)
  have hcomp :
      iteratedFDeriv ℝ n (G ∘ L) t =
        (iteratedFDeriv ℝ n G (L t)).compContinuousLinearMap
          (fun _ : Fin n => L) :=
    L.iteratedFDeriv_comp_right hG t le_top
  have htranslate :
      iteratedFDeriv ℝ n G (L t) =
        iteratedFDeriv ℝ n F (x, t) := by
    exact iteratedFDeriv_comp_add_left n A (L t)
  exact Eq.subst
    (motive := fun q : ℝ → ℂ =>
      iteratedFDeriv ℝ n q t =
        (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
          (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding))
    hline.symm
    (Eq.subst
      (motive := fun v : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℂ =>
        iteratedFDeriv ℝ n (G ∘ L) t =
          v.compContinuousLinearMap
            (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding))
      htranslate
      hcomp)

/-- Applying a vertical-line Frechet derivative to scalar unit directions is applying the
ambient Frechet derivative to vertical parameter directions. -/
theorem iteratedFDeriv_verticalLine_apply_ones_eq_verticalDirections
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    (iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t :
        (Fin n → ℝ) → ℂ)
      (fun _ : Fin n => 1) =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  have hcomp :
      iteratedFDeriv ℝ n (fun u : ℝ => F (x, u)) t =
        (iteratedFDeriv ℝ n F (x, t)).compContinuousLinearMap
          (fun _ : Fin n => zetaPaleyWienerVerticalLinearEmbedding) :=
    iteratedFDeriv_verticalLine_eq_comp_verticalLinearEmbedding F hF n x t
  exact Eq.trans
    (congrArg
      (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ =>
        L (fun _ : Fin n => 1))
      hcomp)
    (congrArg
      (fun m : Fin n → ℝ × ℝ =>
        (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ) m)
      (funext
        (fun _i : Fin n =>
          zetaPaleyWienerVerticalLinearEmbedding_one)))

/-- Generic vertical-line compatibility between one-variable iterated derivatives and
ambient Frechet derivatives evaluated repeatedly on the vertical parameter direction. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedDeriv n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  exact Eq.trans
    (iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ) (n := n)
      (f := fun u : ℝ => F (x, u)) (x := t))
    (iteratedFDeriv_verticalLine_apply_ones_eq_verticalDirections
      F hF n x t)

/-- The successor step for generic vertical-line compatibility between one-variable
iterated derivatives and repeated vertical Frechet derivatives. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_succ
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ)
    (ih :
      ∀ x t : ℝ,
        iteratedDeriv n (fun u : ℝ => F (x, u)) t =
          (iteratedFDeriv ℝ n F (x, t) :
              (Fin n → ℝ × ℝ) → ℂ)
            (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection))
    (x t : ℝ) :
    iteratedDeriv (Nat.succ n) (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ (Nat.succ n) F (x, t) :
          (Fin (Nat.succ n) → ℝ × ℝ) → ℂ)
        (fun _ : Fin (Nat.succ n) => zetaPaleyWienerVerticalParameterDirection) := by
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    F hF (Nat.succ n) x t

/-- Generic vertical-line compatibility between one-variable iterated derivatives and
iterated Frechet derivatives evaluated on the repeated vertical direction. -/
theorem iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection
    (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x t : ℝ) :
    iteratedDeriv n (fun u : ℝ => F (x, u)) t =
      (iteratedFDeriv ℝ n F (x, t) :
          (Fin n → ℝ × ℝ) → ℂ)
        (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection) := by
  exact iteratedDeriv_verticalLine_eq_iteratedFDeriv_verticalDirection_direct
    F hF n x t

/-- The canonical two-variable jet of the horizontal twist in the vertical direction. -/
noncomputable def zetaPaleyWienerHorizontalTwistVerticalJet
    (f : ZetaAdmissibleFunction) (n : ℕ) (x t : ℝ) : ℂ :=
  (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f) (x, t) :
      (Fin n → ℝ × ℝ) → ℂ)
    (fun _ : Fin n => zetaPaleyWienerVerticalParameterDirection)

/-- The zero-th vertical parameter jet is the horizontal twist itself. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_zero
    (f : ZetaAdmissibleFunction) (x t : ℝ) :
    zetaPaleyWienerHorizontalTwistVerticalJet f 0 x t =
      zetaPaleyWienerHorizontalTwist f x t := by
  exact iteratedFDeriv_zero_apply
    (f := zetaPaleyWienerHorizontalTwistParameter f)
    (x := (x, t))
    (m := fun i : Fin 0 => zetaPaleyWienerVerticalParameterDirection)

/-- The horizontal twist is smooth as a two-variable function of `(x,t)`. -/
theorem zetaPaleyWienerHorizontalTwistParameter_contDiff
    (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (zetaPaleyWienerHorizontalTwistParameter f) := by
  have hsource :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => f.toZetaTestFunction' p.2) :=
    f.smooth.comp contDiff_snd
  have hmul :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  have hexp_real :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (p.1 * p.2)) :=
    Real.contDiff_exp.comp hmul
  have hexp_complex :
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.exp (p.1 * p.2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hexp_real
  unfold zetaPaleyWienerHorizontalTwistParameter
  unfold zetaPaleyWienerHorizontalTwist
  exact hsource.mul hexp_complex

/-- The parameter twist restricted to a vertical affine line is smooth. -/
theorem zetaPaleyWienerHorizontalTwistParameter_verticalLine_contDiff
    (f : ZetaAdmissibleFunction) (x : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ =>
        zetaPaleyWienerHorizontalTwistParameter f
          (zetaPaleyWienerVerticalLineEmbedding x t)) := by
  exact (zetaPaleyWienerHorizontalTwistParameter_contDiff f).comp
    (zetaPaleyWienerVerticalLineEmbedding_contDiff x)

/-- The vertical parameter jet is continuous on the full parameter plane. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_continuous
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    Continuous
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) := by
  have hjet :
      Continuous
        (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f)) :=
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f).continuous_iteratedFDeriv
      n le_top
  have hdirection :
      Continuous
        (fun _p : ℝ × ℝ =>
          (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)) :=
    continuous_const
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact continuous_eval.comp (hjet.prod_mk hdirection)

/-- The vertical parameter jet is smooth on the full parameter plane. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_contDiff
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2) := by
  have hjet :
      ContDiff ℝ ∞
        (iteratedFDeriv ℝ n (zetaPaleyWienerHorizontalTwistParameter f)) :=
    (zetaPaleyWienerHorizontalTwistParameter_contDiff f).iteratedFDeriv_right
      le_top
  have happly :
      ContDiff ℝ ∞
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) ℂ =>
          L (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)) := by
    exact (ContinuousMultilinearMap.apply
      ℝ
      (fun _ : Fin n => ℝ × ℝ)
      ℂ
      (fun _i : Fin n => zetaPaleyWienerVerticalParameterDirection)).contDiff
  unfold zetaPaleyWienerHorizontalTwistVerticalJet
  exact happly.comp hjet

/-- The vertical parameter jet is continuous on the compact parameter-support rectangle. -/
theorem zetaPaleyWienerHorizontalTwistVerticalJet_continuousOn_rectangle
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2)
      (zetaPaleyWienerParameterSupportRectangle I a b) := by
  exact (zetaPaleyWienerHorizontalTwistVerticalJet_continuous f n).continuousOn

/-- Compact-rectangle boundedness for the vertical parameter jet. -/
theorem exists_zetaPaleyWienerHorizontalTwistVerticalJet_rectangleBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ p : ℝ × ℝ,
        p ∈ zetaPaleyWienerParameterSupportRectangle I a b →
        ‖zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      (zetaPaleyWienerParameterSupportRectangle_isCompact I a b)
      (zetaPaleyWienerHorizontalTwistVerticalJet_continuousOn_rectangle
        f I a b n) with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, weightedLaplaceKernel_positive_bump C0, ?_⟩
  intro p hp
  have hraw :
      ‖zetaPaleyWienerHorizontalTwistVerticalJet f n p.1 p.2‖ ≤ C0 :=
    hC0 p hp
  exact weightedLaplaceKernel_bound_le_bump C0 hraw

/-- Coordinate form of compact-rectangle boundedness for the vertical parameter jet. -/
theorem exists_zetaPaleyWienerHorizontalTwistVerticalJet_intervalBound
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x : ℝ,
        a ≤ x →
        x ≤ b →
        ∀ t : ℝ,
          I.lower ≤ t →
          t ≤ I.upper →
          ‖zetaPaleyWienerHorizontalTwistVerticalJet f n x t‖ ≤ C := by
  rcases exists_zetaPaleyWienerHorizontalTwistVerticalJet_rectangleBound
      f I a b n with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro x hx_left hx_right t ht_lower ht_upper
  have hp :
      (x, t) ∈ zetaPaleyWienerParameterSupportRectangle I a b := by
    exact ⟨⟨hx_left, hx_right⟩, ⟨ht_lower, ht_upper⟩⟩
  exact hCbound (x, t) hp

/-- A point of the real line is either inside the certified support interval or strictly
outside one of its two sides. -/
theorem zetaPaleyWienerSupportInterval_inside_or_outside
    (I : ZetaPaleyWienerSupportInterval f) (t : ℝ) :
    (I.lower ≤ t ∧ t ≤ I.upper) ∨ t < I.lower ∨ I.upper < t := by
  by_cases ht_lower : I.lower ≤ t
  · by_cases ht_upper : t ≤ I.upper
    · exact Or.inl ⟨ht_lower, ht_upper⟩
    · exact Or.inr (Or.inr (lt_of_not_ge ht_upper))
  · exact Or.inr (Or.inl (lt_of_not_ge ht_lower))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
