import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.FiniteSample.OwnerParts.Part01_FiniteSamples

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction
noncomputable section

/-- Subtracting the old cardinal interpolation of an admissible function kills all old
sample values. -/
theorem zetaLaplaceTransform_cardinalCorrection_vanishes_on_oldSamples
    (T : Finset ℂ) (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction) :
    ∀ w : T,
      Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        (w : ℂ) = 0 := by
  intro w
  let correction : ZetaAdmissibleFunction :=
    ∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z
  have hcorrection :
      zetaLaplaceTransformFiniteSample T correction =
        zetaLaplaceTransformFiniteSample T h := by
    exact zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
      T (zetaLaplaceTransformFiniteSample T h) Ftail hFtail
  calc
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) • correction).toZetaTestFunction'
        (w : ℂ) =
        zetaLaplaceTransformFiniteSample T (h + (-1 : ℂ) • correction) w := by
      rfl
    _ =
        (zetaLaplaceTransformFiniteSample T h +
          zetaLaplaceTransformFiniteSample T ((-1 : ℂ) • correction)) w := by
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add T h ((-1 : ℂ) • correction))
        w
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          zetaLaplaceTransformFiniteSample T ((-1 : ℂ) • correction) w := by
      rfl
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          ((-1 : ℂ) • zetaLaplaceTransformFiniteSample T correction) w := by
      exact congrArg
        (fun u : ℂ => zetaLaplaceTransformFiniteSample T h w + u)
        (congrFun
          (zetaLaplaceTransformFiniteSample_smul T (-1 : ℂ) correction)
          w)
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          (-1 : ℂ) * zetaLaplaceTransformFiniteSample T correction w := by
      rfl
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          (-1 : ℂ) * zetaLaplaceTransformFiniteSample T h w := by
      exact congrArg
        (fun u : ℂ =>
          zetaLaplaceTransformFiniteSample T h w + (-1 : ℂ) * u)
        (congrFun hcorrection w)
    _ =
        zetaLaplaceTransformFiniteSample T h w +
          -(zetaLaplaceTransformFiniteSample T h w) := by
      exact congrArg
        (fun u : ℂ => zetaLaplaceTransformFiniteSample T h w + u)
        (neg_eq_neg_one_mul
          (zetaLaplaceTransformFiniteSample T h w)).symm
    _ = 0 := by
      exact add_neg_cancel (zetaLaplaceTransformFiniteSample T h w)

/-- The new-sample value of the corrected separator is the residual after subtracting
the old cardinal interpolation. -/
theorem zetaLaplaceTransform_cardinalCorrection_at_newSample
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        a =
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
  let correction : ZetaAdmissibleFunction :=
    ∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z
  have hCorrectionAt :
      Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a =
        ∑ z : T,
          zetaLaplaceTransformFiniteSample T h z *
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
    let S : Finset ℂ := {a}
    let za : S := ⟨a, Finset.mem_singleton_self a⟩
    calc
      Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a =
          zetaLaplaceTransformFiniteSample S correction za := by
        rfl
      _ =
          (∑ z : T,
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z)) za := by
        exact congrFun
          (zetaLaplaceTransformFiniteSample_sum
            S Finset.univ
            (fun z : T => zetaLaplaceTransformFiniteSample T h z • Ftail z))
          za
      _ =
          ∑ z : T,
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z) za := by
        exact Finset.univ.sum_apply za
          (fun z : T =>
            zetaLaplaceTransformFiniteSample S
              (zetaLaplaceTransformFiniteSample T h z • Ftail z))
      _ =
          ∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
        exact Finset.sum_congr rfl
          (fun z _hz =>
            calc
              zetaLaplaceTransformFiniteSample S
                  (zetaLaplaceTransformFiniteSample T h z • Ftail z) za =
                  (zetaLaplaceTransformFiniteSample T h z •
                    zetaLaplaceTransformFiniteSample S (Ftail z)) za := by
                exact congrFun
                  (zetaLaplaceTransformFiniteSample_smul
                    S (zetaLaplaceTransformFiniteSample T h z) (Ftail z))
                  za
              _ =
                  zetaLaplaceTransformFiniteSample T h z *
                    zetaLaplaceTransformFiniteSample S (Ftail z) za := by
                rfl
              _ =
                  zetaLaplaceTransformFiniteSample T h z *
                    Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a := by
                rfl)
  calc
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) • correction).toZetaTestFunction'
        a =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          Boundary.zetaLaplaceTransform ((-1 : ℂ) • correction).toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrFun
        (zetaLaplaceTransformFiniteSample_add S h ((-1 : ℂ) • correction))
        za
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) * Boundary.zetaLaplaceTransform correction.toZetaTestFunction' a := by
      let S : Finset ℂ := {a}
      let za : S := ⟨a, Finset.mem_singleton_self a⟩
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a + u)
        (congrFun
          (zetaLaplaceTransformFiniteSample_smul S (-1 : ℂ) correction)
          za)
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
            (-1 : ℂ) * u)
        hCorrectionAt

/-- A function whose old-cardinal correction has nonzero residual at the new sample gives
an analytic separator for that new sample. -/
theorem exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction)
    (hResidual :
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) ≠ 0) :
    ∃ g : ZetaAdmissibleFunction,
      (∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0) ∧
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
  let g : ZetaAdmissibleFunction :=
    h + (-1 : ℂ) •
      (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)
  have hgOld :
      ∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0 :=
    zetaLaplaceTransform_cardinalCorrection_vanishes_on_oldSamples
      T Ftail hFtail h
  have hgNew :
      Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
    intro hzero
    exact hResidual
      ((zetaLaplaceTransform_cardinalCorrection_at_newSample
        T a Ftail h).symm.trans hzero)
  exact ⟨g, hgOld, hgNew⟩

/-- Corrected residual witnesses at every insertion step constructively build cardinal
families on all finite spectral sample sets. -/
theorem exists_zetaLaplaceTransformCardinalFamily_of_correctedWitnesses
    (hWitness :
      ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
        ∀ Ftail : T → ZetaAdmissibleFunction,
          (∀ z w : T,
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
              if w = z then 1 else 0) →
            ∃ h : ZetaAdmissibleFunction,
              Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
                (-1 : ℂ) *
                  (∑ z : T,
                    zetaLaplaceTransformFiniteSample T h z *
                      Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) ≠ 0) :
    ∀ S : Finset ℂ,
      ∃ F : S → ZetaAdmissibleFunction,
        ∀ z w : S,
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
            if w = z then 1 else 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      exact exists_zetaLaplaceTransformCardinalFamily_empty_ownerPaleyWiener
  | @insert a T ha ih =>
      match ih with
      | ⟨Ftail, hFtail⟩ =>
          match hWitness T a ha Ftail hFtail with
          | ⟨h, hResidual⟩ =>
              match
                  exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
                    T a Ftail hFtail h hResidual with
              | ⟨g, hgOld, hgNew⟩ =>
                  exact
                    exists_zetaLaplaceTransformCardinalFamily_insert_of_cardinalFamily_and_separator
                      T a ha Ftail hFtail g hgOld hgNew

/-- The corrected residual functional attached to an old cardinal family and a new
sample. This is the finite-correspondence coefficient left after subtracting the old
cardinal interpolation from an admissible probe. -/
def zetaLaplaceTransformCorrectedResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) : ℂ :=
  Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
    (-1 : ℂ) *
      (∑ z : T,
        zetaLaplaceTransformFiniteSample T h z *
          Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a)

/-- The corrected residual is exactly the new-sample value of the corrected probe. -/
theorem zetaLaplaceTransform_cardinalCorrection_at_newSample_eq_correctedResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    Boundary.zetaLaplaceTransform
        (h + (-1 : ℂ) •
          (∑ z : T, zetaLaplaceTransformFiniteSample T h z • Ftail z)).toZetaTestFunction'
        a =
      zetaLaplaceTransformCorrectedResidual T a Ftail h := by
  exact zetaLaplaceTransform_cardinalCorrection_at_newSample T a Ftail h

/-- A nonzero corrected residual is precisely the concrete witness needed for the
constructive cardinal-family insertion step. -/
theorem exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_nonzeroResidual
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hFtail :
      ∀ z w : T,
        Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0)
    (h : ZetaAdmissibleFunction)
    (hResidual :
      zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0) :
    ∃ g : ZetaAdmissibleFunction,
      (∀ w : T,
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' (w : ℂ) = 0) ∧
        Boundary.zetaLaplaceTransform g.toZetaTestFunction' a ≠ 0 := by
  exact
    exists_zetaLaplaceTransformSeparator_of_cardinalFamily_and_correctedWitness
      T a Ftail hFtail h hResidual

/-- Nonzero corrected residual witnesses at every insertion step constructively build
cardinal families on all finite spectral sample sets. -/
theorem exists_zetaLaplaceTransformCardinalFamily_of_nonzeroCorrectedResiduals
    (hWitness :
      ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
        ∀ Ftail : T → ZetaAdmissibleFunction,
          (∀ z w : T,
            Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' (w : ℂ) =
              if w = z then 1 else 0) →
            ∃ h : ZetaAdmissibleFunction,
              zetaLaplaceTransformCorrectedResidual T a Ftail h ≠ 0) :
    ∀ S : Finset ℂ,
      ∃ F : S → ZetaAdmissibleFunction,
        ∀ z w : S,
          Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
            if w = z then 1 else 0 := by
  exact
    exists_zetaLaplaceTransformCardinalFamily_of_correctedWitnesses
      (fun T a ha Ftail hFtail =>
        hWitness T a ha Ftail hFtail)

/-- The coefficient on the new sample in the residual finite exponential distribution is
one. -/
def zetaLaplaceTransformCorrectedResidualCoefficient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) : ℂ :=
  if hz : (z : ℂ) = a then
    1
  else
    -(Boundary.zetaLaplaceTransform
        (Ftail
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩).toZetaTestFunction'
        a)

/-- The residual coefficient at the newly inserted sample is exactly one. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_new
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualCoefficient
        T a Ftail ⟨a, Finset.mem_insert_self a T⟩ = 1 := by
  exact dif_pos rfl

/-- The residual coefficient at an old sample is minus the old cardinal value at the new
sample. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_old
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) (hz : (z : ℂ) ≠ a) :
    zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z =
      -(Boundary.zetaLaplaceTransform
        (Ftail
          ⟨(z : ℂ), (Finset.mem_insert.mp z.property).resolve_left hz⟩).toZetaTestFunction'
        a) := by
  exact dif_neg hz

/-- The residual coefficient family is explicitly nonzero at the newly inserted sample. -/
theorem zetaLaplaceTransformCorrectedResidualCoefficient_nonzero
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualCoefficient
        T a Ftail ⟨a, Finset.mem_insert_self a T⟩ ≠ 0 := by
  intro honeZero
  have hone :
      (1 : ℂ) = 0 := by
    exact
      (zetaLaplaceTransformCorrectedResidualCoefficient_new
        T a Ftail).symm.trans honeZero
  exact one_ne_zero hone

/-- The same corrected-residual coefficient written on the ambient spectral plane.
It is supported on `insert a T`, equals one at the new sample, and equals minus the old
cardinal row evaluated at the new sample on the old support. -/
def zetaLaplaceTransformCorrectedResidualAmbientCoefficient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : ℂ) : ℂ :=
  if hz : z = a then
    1
  else
    if hT : z ∈ T then
      -(Boundary.zetaLaplaceTransform
        (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
    else
      0

/-- The ambient residual coefficient at the newly inserted sample is one. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_new
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail a = 1 := by
  exact dif_pos rfl

/-- The ambient residual coefficient at an old sample is minus the old cardinal value at
the new sample. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
    (T : Finset ℂ) (a z : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hzT : z ∈ T) (hza : z ≠ a) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
      -(Boundary.zetaLaplaceTransform
        (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
  calc
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
        if hT : z ∈ T then
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
        else
          0 := by
      exact dif_neg hza
    _ =
        -(Boundary.zetaLaplaceTransform
          (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
      exact dif_pos hzT

/-- The ambient residual coefficient vanishes away from the inserted finite support. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_offSupport
    (T : Finset ℂ) (a z : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (hza : z ≠ a) (hzT : z ∉ T) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z = 0 := by
  calc
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z =
        if hT : z ∈ T then
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨z, hT⟩).toZetaTestFunction' a)
        else
          0 := by
      exact dif_neg hza
    _ = 0 := by
      exact dif_neg hzT

/-- On the inserted support, the ambient and subtype residual coefficients agree. -/
theorem zetaLaplaceTransformCorrectedResidualAmbientCoefficient_subtype
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) :
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
      zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  if hz : (z : ℂ) = a then
    calc
      zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
          1 := by
        exact dif_pos hz
      _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
        have hzSub : z = ⟨a, Finset.mem_insert_self a T⟩ := by
          exact Subtype.ext hz
        calc
          (1 : ℂ) =
              zetaLaplaceTransformCorrectedResidualCoefficient
                T a Ftail ⟨a, Finset.mem_insert_self a T⟩ := by
            exact (zetaLaplaceTransformCorrectedResidualCoefficient_new T a Ftail).symm
          _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
            exact congrArg
              (fun u : {z : ℂ // z ∈ insert a T} =>
                zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail u)
              hzSub.symm
  else
    let hT : (z : ℂ) ∈ T := (Finset.mem_insert.mp z.property).resolve_left hz
    calc
      zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
          -(Boundary.zetaLaplaceTransform
            (Ftail ⟨(z : ℂ), hT⟩).toZetaTestFunction' a) := by
        exact
          zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
            T a (z : ℂ) Ftail hT hz
      _ = zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
        exact (zetaLaplaceTransformCorrectedResidualCoefficient_old
          T a Ftail z hz).symm

/-- The corrected residual is the pairing of the admissible Laplace samples with the
ambient finite exponential-distribution coefficient supported on `insert a T`. -/
theorem zetaLaplaceTransformCorrectedResidual_eq_ambientCoefficient_sum
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
      ∑ z in insert a T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
          zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail z := by
  let coeff : ℂ → ℂ :=
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail
  have hnew :
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a := by
    calc
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a =
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * 1 := by
        exact congrArg
          (fun u : ℂ =>
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * u)
          (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_new T a Ftail)
      _ = Boundary.zetaLaplaceTransform h.toZetaTestFunction' a := by
        exact mul_one (Boundary.zetaLaplaceTransform h.toZetaTestFunction' a)
  have hold :
      (∑ z in T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) =
        (-1 : ℂ) *
          (∑ z : T,
            zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
    calc
      (∑ z in T,
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) =
          ∑ z : T,
            -(zetaLaplaceTransformFiniteSample T h z *
              Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
        exact Finset.sum_bij
          (fun z _hz => (⟨z, _hz⟩ : T))
          (fun _ _ => Finset.mem_univ _)
          (fun z₁ _ z₂ _ hsub => congrArg Subtype.val hsub)
          (fun z _hz => ⟨(z : ℂ), z.property, Subtype.ext rfl⟩)
          (fun z hzT =>
            have hza : z ≠ a := fun hza => haT (hza ▸ hzT)
            calc
              Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z =
                  Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
                    (-(Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a)) := by
                exact congrArg
                  (fun u : ℂ =>
                    Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * u)
                  (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_old
                    T a z Ftail hzT hza)
              _ =
                  -(Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
                    Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
                exact mul_neg
                  (Boundary.zetaLaplaceTransform h.toZetaTestFunction' z)
                  (Boundary.zetaLaplaceTransform
                    (Ftail ⟨z, hzT⟩).toZetaTestFunction' a)
              _ =
                  -(zetaLaplaceTransformFiniteSample T h ⟨z, hzT⟩ *
                    Boundary.zetaLaplaceTransform
                      (Ftail ⟨z, hzT⟩).toZetaTestFunction' a) := by
                rfl)
      _ =
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
        exact
          (Finset.sum_neg_distrib
            (s := (Finset.univ : Finset T))
            (f := fun z : T =>
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a)).trans
            (neg_eq_neg_one_mul
              (∑ z : T,
                zetaLaplaceTransformFiniteSample T h z *
                  Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a))
  calc
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (-1 : ℂ) *
            (∑ z : T,
              zetaLaplaceTransformFiniteSample T h z *
                Boundary.zetaLaplaceTransform (Ftail z).toZetaTestFunction' a) := by
      rfl
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a +
          (∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) := by
      exact congrArg
        (fun u : ℂ => Boundary.zetaLaplaceTransform h.toZetaTestFunction' a + u)
        hold.symm
    _ =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' a * coeff a +
          (∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z) := by
      exact congrArg
        (fun u : ℂ =>
          u + ∑ z in T,
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z)
        hnew.symm
    _ =
        ∑ z in insert a T,
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z := by
      exact
        (Finset.sum_insert
          (s := T)
          (a := a)
          (f := fun z : ℂ =>
            Boundary.zetaLaplaceTransform h.toZetaTestFunction' z * coeff z)
          haT).symm

/-- On the inserted support, the ambient coefficient summand is the subtype
coefficient summand. -/
theorem zetaLaplaceTransformCorrectedResidual_insertCoefficientSummand_eq_ambient
    (T : Finset ℂ) (a : ℂ)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction)
    (z : {z : ℂ // z ∈ insert a T}) :
    Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
        zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
      zetaLaplaceTransformFiniteSample (insert a T) h z *
        zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  calc
    Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
        zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail (z : ℂ) =
        Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
      exact congrArg
        (fun u : ℂ =>
          Boundary.zetaLaplaceTransform h.toZetaTestFunction' (z : ℂ) * u)
        (zetaLaplaceTransformCorrectedResidualAmbientCoefficient_subtype
          T a Ftail z)
    _ =
        zetaLaplaceTransformFiniteSample (insert a T) h z *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
      rfl

/-- The corrected residual is the coefficient pairing over the inserted finite
sample, written with the subtype coefficient family. -/
theorem zetaLaplaceTransformCorrectedResidual_eq_insertCoefficientSum
    (T : Finset ℂ) (a : ℂ) (haT : a ∉ T)
    (Ftail : T → ZetaAdmissibleFunction)
    (h : ZetaAdmissibleFunction) :
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
      ∑ z in (insert a T).attach,
        zetaLaplaceTransformFiniteSample (insert a T) h z *
          zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z := by
  let ambientCoeff : ℂ → ℂ :=
    zetaLaplaceTransformCorrectedResidualAmbientCoefficient T a Ftail
  let ambientSummand : ℂ → ℂ :=
    fun z =>
      Boundary.zetaLaplaceTransform h.toZetaTestFunction' z *
        ambientCoeff z
  let subtypeSummand : {z : ℂ // z ∈ insert a T} → ℂ :=
    fun z =>
      zetaLaplaceTransformFiniteSample (insert a T) h z *
        zetaLaplaceTransformCorrectedResidualCoefficient T a Ftail z
  calc
    zetaLaplaceTransformCorrectedResidual T a Ftail h =
        ∑ z in insert a T, ambientSummand z := by
      exact zetaLaplaceTransformCorrectedResidual_eq_ambientCoefficient_sum
        T a haT Ftail h
    _ =
        ∑ z in (insert a T).attach, subtypeSummand z := by
      exact Finset.sum_bij
        (fun z hz => (⟨z, hz⟩ : {z : ℂ // z ∈ insert a T}))
        (fun _ _ => Finset.mem_attach _ _)
        (fun z₁ _ z₂ _ hSubtype =>
          congrArg Subtype.val hSubtype)
        (fun z _hz => ⟨(z : ℂ), z.property, Subtype.ext rfl⟩)
        (fun z hz =>
          calc
            ambientSummand z =
                subtypeSummand ⟨z, hz⟩ := by
              exact
                zetaLaplaceTransformCorrectedResidual_insertCoefficientSummand_eq_ambient
                  T a Ftail h ⟨z, hz⟩
            _ = subtypeSummand ⟨z, hz⟩ := by
              rfl)

end
end ZetaAdmissibleFunction
end LFunctions
end Boundary
