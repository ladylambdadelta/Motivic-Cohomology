import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteExponentialDetector.Owner

/-!
# Paley-Wiener finite sample interpolation

This file owns the finite Laplace-sample map, Kronecker cardinal vectors, dual
separation, and finite Paley-Wiener interpolation wrappers. It is copy-first
extracted from the current Paley-Wiener owner file, so declaration names
intentionally match the existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction

noncomputable section

/-- The finite Laplace-transform sample vector of an admissible function. -/
def zetaLaplaceTransformFiniteSample
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    S → ℂ :=
  fun z : S => Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ)

/-- The finite target vector induced by a function on the ambient spectral plane. -/
def zetaLaplaceTransformFiniteTarget
    (S : Finset ℂ) (a : ℂ → ℂ) :
    S → ℂ :=
  fun z : S => a (z : ℂ)

/-- The finite Laplace-sample vector of a scalar multiple is the scalar multiple of the
finite Laplace-sample vector. -/
theorem zetaLaplaceTransformFiniteSample_smul
    (S : Finset ℂ) (c : ℂ) (f : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (c • f) =
      c • zetaLaplaceTransformFiniteSample S f := by
  ext z
  have hpoint :
      (c • f).toZetaTestFunction' =
        c • f.toZetaTestFunction' := by
    ext t
    calc
      (c • f).toZetaTestFunction' t =
          (c • f) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (c • f) t
      _ = c * f t := by
        exact ZetaAdmissibleFunction.smul_apply c f t
      _ = c * f.toZetaTestFunction' t := by
        exact congrArg (fun u : ℂ => c * u)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
      _ = (c • f.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (c • f).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (c • f.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
    _ = c * Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_smul c f.toZetaTestFunction' (z : ℂ)
    _ = (c • zetaLaplaceTransformFiniteSample S f) z := by
      rfl

/-- The finite Laplace-sample vector of a sum is the sum of the finite Laplace-sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_add
    (S : Finset ℂ) (f g : ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (f + g) =
      zetaLaplaceTransformFiniteSample S f +
        zetaLaplaceTransformFiniteSample S g := by
  ext z
  have hpoint :
      (f + g).toZetaTestFunction' =
        f.toZetaTestFunction' + g.toZetaTestFunction' := by
    ext t
    calc
      (f + g).toZetaTestFunction' t =
          (f + g) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (f + g) t
      _ = f t + g t := by
        exact ZetaAdmissibleFunction.add_apply f g t
      _ = f.toZetaTestFunction' t + g.toZetaTestFunction' t := by
        exact congrArg₂ (fun u v : ℂ => u + v)
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply f t).symm
          (ZetaAdmissibleFunction.toZetaTestFunction'_apply g t).symm
      _ = (f.toZetaTestFunction' + g.toZetaTestFunction') t := by
        rfl
  calc
    Boundary.zetaLaplaceTransform (f + g).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform
          (f.toZetaTestFunction' + g.toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) +
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_add
        f.toZetaTestFunction'
        g.toZetaTestFunction'
        (z : ℂ)
        (integrable_laplaceKernel_at f (z : ℂ))
        (integrable_laplaceKernel_at g (z : ℂ))
    _ =
        (zetaLaplaceTransformFiniteSample S f +
          zetaLaplaceTransformFiniteSample S g) z := by
      rfl

/-- The finite Laplace-sample map as a bundled linear map. -/
def zetaLaplaceTransformFiniteSampleLinearMap
    (S : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] (S → ℂ) where
  toFun := zetaLaplaceTransformFiniteSample S
  map_add' := fun f g =>
    zetaLaplaceTransformFiniteSample_add S f g
  map_smul' := fun c f =>
    zetaLaplaceTransformFiniteSample_smul S c f

/-- The finite Laplace-sample vector of a finite sum is the finite sum of the sample
vectors. -/
theorem zetaLaplaceTransformFiniteSample_sum
    {α : Type*} [DecidableEq α]
    (S : Finset ℂ) (T : Finset α) (F : α → ZetaAdmissibleFunction) :
    zetaLaplaceTransformFiniteSample S (∑ x in T, F x) =
      ∑ x in T, zetaLaplaceTransformFiniteSample S (F x) := by
  ext z
  have hpoint :
      (∑ x in T, F x).toZetaTestFunction' =
        ∑ x in T, (F x).toZetaTestFunction' := by
    ext t
    calc
      (∑ x in T, F x).toZetaTestFunction' t =
          (∑ x in T, F x) t := by
        exact ZetaAdmissibleFunction.toZetaTestFunction'_apply (∑ x in T, F x) t
      _ = ∑ x in T, F x t := by
        exact ZetaAdmissibleFunction.sum_apply T F t
      _ = (∑ x in T, (F x).toZetaTestFunction') t := by
        exact (Boundary.zetaLaplaceTransform_sum_apply
          (s := T)
          (f := fun x : α => (F x).toZetaTestFunction')
          t).symm
  calc
    Boundary.zetaLaplaceTransform (∑ x in T, F x).toZetaTestFunction' (z : ℂ) =
        Boundary.zetaLaplaceTransform (∑ x in T, (F x).toZetaTestFunction') (z : ℂ) := by
      exact congrFun (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ => congrArg (fun F : ZetaTestFunction => F t) hpoint)) (z : ℂ)
    _ =
        ∑ x in T,
          Boundary.zetaLaplaceTransform (F x).toZetaTestFunction' (z : ℂ) := by
      exact Boundary.zetaLaplaceTransform_sum
        T
        (fun x : α => (F x).toZetaTestFunction')
        (z : ℂ)
        (fun x _hx => integrable_laplaceKernel_at (F x) (z : ℂ))
    _ = (∑ x in T, zetaLaplaceTransformFiniteSample S (F x)) z := by
      exact (T.sum_apply z
        (fun x : α => zetaLaplaceTransformFiniteSample S (F x))).symm

/-- A cardinal family gives the finite linear-combination interpolant for any target
finite sample vector. -/
theorem zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
    (S : Finset ℂ) (aS : S → ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) = aS := by
  ext w
  calc
    zetaLaplaceTransformFiniteSample S (∑ z : S, aS z • F z) w =
        (∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z)) w := by
      exact congrFun
        (zetaLaplaceTransformFiniteSample_sum
          S Finset.univ (fun z : S => aS z • F z))
        w
    _ =
        ∑ z : S, zetaLaplaceTransformFiniteSample S (aS z • F z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => zetaLaplaceTransformFiniteSample S (aS z • F z))
    _ =
        ∑ z : S, aS z *
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrFun (zetaLaplaceTransformFiniteSample_smul S (aS z) (F z)) w)
    _ =
        ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u) (hF z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- A cardinal family constructively realizes every finite sample vector. -/
theorem exists_zetaLaplaceTransformFiniteSample_eq_of_cardinalFamily_ownerPaleyWiener
    (S : Finset ℂ) (aS : S → ℂ)
    (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaLaplaceTransformFiniteSample S f = aS := by
  exact
    ⟨∑ z : S, aS z • F z,
      zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
        S aS F hF⟩

/-- The Kronecker vector for a cardinal probe at one spectral sample. -/
def zetaLaplaceTransformCardinalVector
    (S : Finset ℂ) (z : S) : S → ℂ :=
  fun w : S => if w = z then 1 else 0

/-- The Kronecker vector has the expected value at each finite sample. -/
theorem zetaLaplaceTransformCardinalVector_apply
    (S : Finset ℂ) (z w : S) :
    zetaLaplaceTransformCardinalVector S z w =
      if w = z then 1 else 0 := by
  rfl

/-- Finite-sample realization of every Kronecker vector is exactly a cardinal family. -/
theorem zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z) :
    ∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0 := by
  intro z w
  calc
    Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        zetaLaplaceTransformFiniteSample S (F z) w := by
      rfl
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact congrFun (hF z) w
    _ = if w = z then 1 else 0 := by
      exact zetaLaplaceTransformCardinalVector_apply S z w

/-- A pointwise cardinal family gives finite-sample realization of every Kronecker vector. -/
theorem zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction)
    (hF :
      ∀ z w : S,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ z : S,
      zetaLaplaceTransformFiniteSample S (F z) =
        zetaLaplaceTransformCardinalVector S z := by
  intro z
  ext w
  calc
    zetaLaplaceTransformFiniteSample S (F z) w =
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) := by
      rfl
    _ = if w = z then 1 else 0 := by
      exact hF z w
    _ = zetaLaplaceTransformCardinalVector S z w := by
      exact (zetaLaplaceTransformCardinalVector_apply S z w).symm

/-- Finite-sample cardinal-vector realization is equivalent to the pointwise cardinal
matrix identity. -/
theorem zetaLaplaceTransformCardinalFamily_iff_finiteSample_eq_cardinalVector
    (S : Finset ℂ) (F : S → ZetaAdmissibleFunction) :
    (∀ z w : S,
      Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
        if w = z then 1 else 0) ↔
      ∀ z : S,
        zetaLaplaceTransformFiniteSample S (F z) =
          zetaLaplaceTransformCardinalVector S z := by
  exact
    ⟨zetaLaplaceTransformFiniteSample_eq_cardinalVector_of_cardinalFamily S F,
      zetaLaplaceTransformCardinalFamily_of_finiteSample_eq_cardinalVector S F⟩

/-- The Kronecker cardinal vectors form the standard finite-coordinate expansion of every
finite sample vector. -/
theorem zetaLaplaceTransformCardinalVector_linearCombination
    (S : Finset ℂ) (aS : S → ℂ) :
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) = aS := by
  ext w
  calc
    (∑ z : S, aS z • zetaLaplaceTransformCardinalVector S z) w =
        ∑ z : S, (aS z • zetaLaplaceTransformCardinalVector S z) w := by
      exact Finset.univ.sum_apply w
        (fun z : S => aS z • zetaLaplaceTransformCardinalVector S z)
    _ = ∑ z : S, aS z * (if w = z then 1 else 0) := by
      exact Finset.sum_congr rfl
        (fun z _hz =>
          congrArg (fun u : ℂ => aS z * u)
            (zetaLaplaceTransformCardinalVector_apply S z w))
    _ = aS w := by
      have hsingle :
          ∑ z in (Finset.univ : Finset S),
              aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
        exact Finset.sum_eq_single
          (a := w)
          (f := fun z : S => aS z * (if w = z then 1 else 0))
          (fun z _hz hzw =>
            have hne : w ≠ z := fun hwz => hzw hwz.symm
            calc
              aS z * (if w = z then 1 else 0) =
                  aS z * 0 := by
                exact congrArg (fun u : ℂ => aS z * u) (if_neg hne)
              _ = 0 := by
                exact mul_zero (aS z))
          (fun hw =>
            False.elim (hw (Finset.mem_univ w)))
      calc
        ∑ z : S, aS z * (if w = z then 1 else 0) =
            aS w * (if w = w then 1 else 0) := by
          exact hsingle
        _ = aS w * 1 := by
          exact congrArg (fun u : ℂ => aS w * u) (if_pos rfl)
        _ = aS w := by
          exact mul_one (aS w)

/-- The empty spectral sample set has a vacuous cardinal family. -/
theorem exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener :
    ∃ F : (∅ : Finset ℂ) → ZetaAdmissibleFunction,
      ∀ z w : (∅ : Finset ℂ),
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  exact
    ⟨fun z =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property),
      fun z _w =>
        False.elim (Finset.not_mem_empty (z : ℂ) z.property)⟩

/-- Normalizing a separator makes its Laplace value at the new sample equal to one. -/
theorem zetaLaplaceTransform_normalizedSeparator_at_newSample
    (a : ℂ) (g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a = 1 := by
  let b : ℂ := Boundary.zetaLaplaceTransform g.toZetaTestFunction' a
  calc
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_smul S
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) g)
        za
    _ = b⁻¹ * b := by
      rfl
    _ = 1 := by
      exact inv_mul_cancel₀ hg

/-- Normalizing a separator preserves its zero values on the old sample set. -/
theorem zetaLaplaceTransform_normalizedSeparator_at_oldSample
    (a w : ℂ) (g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' w = 0) :
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        w = 0 := by
  calc
    Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        w =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ *
          Boundary.zetaLaplaceTransform g.toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_smul S
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) g)
        zw
    _ =
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ * 0 := by
      exact congrArg
        (fun u : ℂ =>
          (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ * u)
        hg
    _ = 0 := by
      exact mul_zero
        (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹

/-- The Lagrange update kills the new sample value of an old cardinal function. -/
theorem zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample
    (a : ℂ) (f g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        a = 0 := by
  let x : ℂ := Boundary.zetaLaplaceTransform f.toZetaTestFunction' a
  let y : ℂ := Boundary.zetaLaplaceTransform g.toZetaTestFunction' a
  let c : ℂ :=
    -(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
      (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹
  calc
    Boundary.zetaLaplaceTransform
        (f + c • g).toZetaTestFunction'
        a =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' a +
          Boundary.zetaLaplaceTransform (c • g).toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S f (c • g))
        za
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' a +
          c * Boundary.zetaLaplaceTransform g.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' a + u)
        (congrFun (zetaLaplaceTransformFiniteSample_smul S c g) za)
    _ = x + c * y := by
      rfl
    _ = x + (-(x) * y⁻¹) * y := by
      rfl
    _ = x + -(x) * (y⁻¹ * y) := by
      exact congrArg (fun u : ℂ => x + u) (mul_assoc (-(x)) y⁻¹ y)
    _ = x + -(x) * 1 := by
      exact congrArg (fun u : ℂ => x + -(x) * u) (inv_mul_cancel₀ hg)
    _ = x + -(x) := by
      exact congrArg (fun u : ℂ => x + u) (mul_one (-(x)))
    _ = 0 := by
      exact add_neg_cancel x

/-- The Lagrange update preserves old sample values where the separator vanishes. -/
theorem zetaLaplaceTransform_cardinalUpdate_at_oldSample
    (a w : ℂ) (f g : ZetaAdmissibleFunction)
    (hg :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' w = 0) :
    Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        w =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' w := by
  let c : ℂ :=
    -(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
      (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹
  calc
    Boundary.zetaLaplaceTransform
        (f + c • g).toZetaTestFunction'
        w =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w +
          Boundary.zetaLaplaceTransform (c • g).toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S f (c • g))
        zw
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w +
          c * Boundary.zetaLaplaceTransform g.toZetaTestFunction' w := by
      let S : Finset ℂ := {w}
      let zw : S := ⟨w, Finset.mem_singleton_self w⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + u)
        (congrFun (zetaLaplaceTransformFiniteSample_smul S c g) zw)
    _ =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + c * 0 := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + c * u)
        hg
    _ = Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + 0 := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform f.toZetaTestFunction' w + u)
        (mul_zero c)
    _ = Boundary.zetaLaplaceTransform f.toZetaTestFunction' w := by
      exact add_zero
        (Boundary.zetaLaplaceTransform f.toZetaTestFunction' w)

/-- A normalized separator is the new cardinal row against the old sample set. -/
theorem zetaLaplaceTransform_normalizedSeparator_cardinalRow
    (T : Finset ℂ) (a : ℂ) (g : ZetaAdmissibleFunction)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    (Boundary.zetaLaplaceTransform
        ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
        a = 1) ∧
      ∀ w : T,
        Boundary.zetaLaplaceTransform
          ((Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g).toZetaTestFunction'
          (w : ℂ) = 0 := by
  exact
    ⟨zetaLaplaceTransform_normalizedSeparator_at_newSample a g hgNew,
      fun w =>
        zetaLaplaceTransform_normalizedSeparator_at_oldSample
          a (w : ℂ) g (hgOld w)⟩

/-- Updating an old cardinal row keeps its old finite-sample values and kills the new
sample. -/
theorem zetaLaplaceTransform_cardinalUpdate_oldRow
    (T : Finset ℂ) (a : ℂ) (z : T)
    (f g : ZetaAdmissibleFunction)
    (hf :
      ∀ w : T,
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    (Boundary.zetaLaplaceTransform
        (f +
          (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
              (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
        a = 0) ∧
      ∀ w : T,
        Boundary.zetaLaplaceTransform
          (f +
            (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
                (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
          (w : ℂ) =
            if w = z then 1 else 0 := by
  exact
    ⟨zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample a f g hgNew,
      fun w =>
        calc
          Boundary.zetaLaplaceTransform
            (f +
              (-(Boundary.zetaLaplaceTransform f.toZetaTestFunction' a) *
                  (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g).toZetaTestFunction'
            (w : ℂ) =
              Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ) := by
            exact zetaLaplaceTransform_cardinalUpdate_at_oldSample
              a (w : ℂ) f g (hgOld w)
          _ = if w = z then 1 else 0 := by
            exact hf w⟩

/-- A cardinal family extends across one new sample once an analytic separator for the
new sample is available. -/
theorem exists_zetaLaplaceTransformCardinalFamily_insert_of_cardinalFamily_and_separator
    (T : Finset ℂ) (a : ℂ) (ha : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (g : ZetaAdmissibleFunction)
    (hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0)
    (hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0) :
    ∃ F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction,
      ∀ z w : {z : ℂ // z ∈ insert a T},
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 := by
  let normalizedSeparator : ZetaAdmissibleFunction :=
    (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹ • g
  let oldRowUpdate : T → ZetaAdmissibleFunction :=
    fun z =>
      Ftail z +
        (-(Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) *
            (Boundary.zetaLaplaceTransform g.toZetaTestFunction' a)⁻¹) • g
  let restrictOld :
      ∀ z : {z : ℂ // z ∈ insert a T}, (z : ℂ) ≠ a → T :=
    fun z hz =>
      ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩
  let F : {z : ℂ // z ∈ insert a T} → ZetaAdmissibleFunction :=
    fun z =>
      if hz : (z : ℂ) = a then
        normalizedSeparator
      else
        oldRowUpdate (restrictOld z hz)
  exact ⟨F, fun z w =>
    if hz : (z : ℂ) = a then
      have hFz :
          F z = normalizedSeparator := by
        exact dif_pos hz
      if hw : (w : ℂ) = a then
        have hzw : w = z := by
          exact Subtype.ext (hw.trans hz.symm)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' a := by
            exact congrArg
              (fun u : ℂ =>
                Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' u)
              hw
          _ = 1 := by
            exact zetaLaplaceTransform_normalizedSeparator_at_newSample a g hgNew
          _ = if w = z then 1 else 0 := by
            exact (if_pos hzw).symm
      else
        let wOld : T := restrictOld w hw
        have hzw_ne : w ≠ z := by
          intro hzw
          exact hw ((congrArg Subtype.val hzw).trans hz)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform normalizedSeparator.toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = 0 := by
            exact zetaLaplaceTransform_normalizedSeparator_at_oldSample
              a (w : ℂ) g (hgOld wOld)
          _ = if w = z then 1 else 0 := by
            exact (if_neg hzw_ne).symm
    else
      let zOld : T := restrictOld z hz
      have hFz :
          F z = oldRowUpdate zOld := by
        exact dif_neg hz
      if hw : (w : ℂ) = a then
        have hzw_ne : w ≠ z := by
          intro hzw
          exact hz ((congrArg Subtype.val hzw).symm.trans hw)
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' a := by
            exact congrArg
              (fun u : ℂ =>
                Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' u)
              hw
          _ = 0 := by
            exact zetaLaplaceTransform_cardinalUpdate_vanishes_at_newSample
              a (Ftail zOld) g hgNew
          _ = if w = z then 1 else 0 := by
            exact (if_neg hzw_ne).symm
      else
        let wOld : T := restrictOld w hw
        calc
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
              Boundary.zetaLaplaceTransform (oldRowUpdate zOld).toZetaTestFunction' (w : ℂ) := by
            exact congrArg
              (fun f : ZetaAdmissibleFunction =>
                Boundary.zetaLaplaceTransform f.toZetaTestFunction' (w : ℂ))
              hFz
          _ = if wOld = zOld then 1 else 0 := by
            exact
              (zetaLaplaceTransform_cardinalUpdate_oldRow
                T a zOld (Ftail zOld) g
                (fun u => hFtail zOld u) hgOld hgNew).2 wOld
          _ = if w = z then 1 else 0 := by
            if hOld : wOld = zOld then
              have hInsert : w = z := by
                have hval : (wOld : ℂ) = (zOld : ℂ) :=
                  congrArg (fun u : T => (u : ℂ)) hOld
                exact Subtype.ext hval
              calc
                (if wOld = zOld then (1 : ℂ) else 0) = 1 := by
                  exact if_pos hOld
                _ = if w = z then (1 : ℂ) else 0 := by
                  exact (if_pos hInsert).symm
            else
              have hInsert : w ≠ z := by
                intro hEq
                have hval : (wOld : ℂ) = (zOld : ℂ) :=
                  congrArg (fun u : {z : ℂ // z ∈ insert a T} => (u : ℂ)) hEq
                exact hOld (Subtype.ext hval)
              calc
                (if wOld = zOld then (1 : ℂ) else 0) = 0 := by
                  exact if_neg hOld
                _ = if w = z then (1 : ℂ) else 0 := by
                  exact (if_neg hInsert).symm⟩

end
end ZetaAdmissibleFunction
end LFunctions
end Boundary
