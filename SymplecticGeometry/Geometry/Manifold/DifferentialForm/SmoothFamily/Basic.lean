/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Smooth families of forms

A family `α : N → SmoothForm I M F k` of smooth forms on `M`, indexed by the points of a parameter
manifold `N` (in the uses, `unitInterval` or `ℝ`), is smooth (`SymplecticGeometry.IsSmoothFamily`)
when there is a smooth form `Ω` on `N × M` with `α t = ι_t^* Ω` for every `t`, where
`ι_t : y ↦ (t, y)`. Such a family is read through its *slice section*
`(t, y) ↦ (α t) y`, a section along the projection `N × M → M`.

The slice section of a family of slices is smooth (Tau Ceti's
`TauCeti.contMDiff_mpullback_prodMk_form`). Conversely, if the slice section of `α` is smooth,
then the form on `N × M` whose value at `(t, y)` is the pullback of `α t` along the projection
to `M` is smooth (`TauCeti.SmoothForm.ofSlices`), and its slices are the `α t`. So a family is
smooth exactly when its slice section is (`SymplecticGeometry.isSmoothFamily_iff_contMDiff`).
This makes smoothness of a family a local property in `M`, and gives the closure properties of
smooth families: under the linear operations, multiplication by smooth functions of the parameter
or of the point, pullback along smooth maps, the exterior derivative, cut-off and extension by
zero from an open subset, and reparametrization; and smoothness on `U ⊔ V` is smoothness on `U`
and on `V`.

Families live on `N × M`, the parameter first. A form on `M × N` is turned around by Mathlib's
`Diffeomorph.prodComm`, and its slices are then its pullbacks along `x ↦ (x, t)`
(`TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodComm`).

## Main definitions

* `SymplecticGeometry.IsSmoothFamily J α`: the family `α` is the family of slices of a smooth form
  on `N × M`.
* `TauCeti.SmoothForm.ofSlices α hα`: the smooth form on `N × M` with slices `α t`, for a family
  with a smooth slice section.

## Main results

* `SymplecticGeometry.isSmoothFamily_iff_contMDiff`: a family is smooth exactly when its slice
  section is smooth.
* `SymplecticGeometry.IsSmoothFamily.contMDiff_apply`: the values of a smooth family at a point,
  on fixed tangent vectors, are smooth in the parameter.
* `SymplecticGeometry.IsSmoothFamily.ext_on`: two smooth families that agree on a dense set of
  parameters are equal.
* `SymplecticGeometry.isSmoothFamily_mpullback_prodMk`: the slices of a form on `N × M` are a
  smooth family.
* `SymplecticGeometry.isSmoothFamily_const` and the closure lemmas `IsSmoothFamily.add`, `.neg`,
  `.sub`, `.smul`, `.fun_smul`, `.funSMul`, `.sum`, `.mpullback`, `.mpullback_family`,
  `.mextDeriv`, `.extendByZero_smul` and `.comp`.
* `SymplecticGeometry.isSmoothFamily_interiorₗ`: the contractions of a two-form with a jointly
  smooth family of vector fields form a smooth family of one-forms.
* `SymplecticGeometry.isSmoothFamily_iff_mpullback_inclusion_sup`: smoothness of a family on
  `U ⊔ V` is smoothness of its restrictions to `U` and to `V`.
* `TauCeti.SmoothForm.mpullback_prodMk_mpullback_prodComm`: slices of a form on `M × N` turned
  around by `Diffeomorph.prodComm`.

## Implementation notes

The pullback of a family of forms along a family of maps
(`ContMDiffAt.mpullback_form_family_of_family`) is proved as Tau Ceti's
`ContMDiffAt.mpullback_form_family`, which is its case of a fixed form, with the coefficients of
the family in place of those of the form. The form with prescribed slices is smooth by this
lemma (`TauCeti.contMDiffAt_fun_mpullback_snd_iff`). The constant family is the pullback along
the projection (`TauCeti.SmoothForm.mpullback_prodMk_mpullback_snd`), as in Tau Ceti's
`TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`. Locality in `M` comes from Tau Ceti's
`IsLocalDiffeomorphAt.contMDiffAt_mpullback_form_iff`, applied to `id × (U ↪ W)`, and the proof
of `SymplecticGeometry.IsSmoothFamily.extendByZero_smul` follows that of Tau Ceti's
`TauCeti.IsSmoothForm.extendByZero`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Theorem 3.2.4 (smooth families of forms, in Moser's argument).
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section Family

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  {m n : WithTop ℕ∞}

/-- **Pullback of a family of forms along a family of maps.** Let `f : N → M → M'` be jointly
`C^n` at `(p₀, g p₀)` and `g : N → M` be `C^m` at `p₀`, with `m + 1 ≤ n`, and let `φ` be a family
of rough forms on `M'` over `N` such that `p ↦ φ p (f p (g p))` is a `C^m` section along
`p ↦ f p (g p)` at `p₀`. Then the pullbacks `(f p)^* (φ p)` at `g p` form a `C^m` section along
`g` at `p₀`. -/
theorem _root_.ContMDiffAt.mpullback_form_family_of_family {φ : N → RoughForm I' M' F k}
    {f : N → M → M'} {g : N → M} {p₀ : N}
    (hφ : ContMDiffAt J (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M' ↦ TangentSpace I' y [⋀^Fin k]→L[ℝ] Trivial M' F y) (f p (g p))
        (φ p (f p (g p)))) p₀)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (p₀, g p₀))
    (hg : ContMDiffAt J I m g p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) (g p)
        (mpullback I I' (f p) (φ p) (g p))) p₀ := by
  have hfg : ContMDiffAt J I' m (fun p ↦ f p (g p)) p₀ :=
    (hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)).comp p₀
      (contMDiffAt_id.prodMk hg)
  have hc := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hφ).2
  have hd := hf.mfderiv f g hg hmn
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffAt hd).clm_apply hc
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨hg, hp.congr_of_eventuallyEq ?_⟩
  have hmem : (fun p ↦ f p (g p)) ⁻¹'
      (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet ∈ 𝓝 p₀ :=
    hfg.continuousAt.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f p₀ (g p₀))))
  filter_upwards [hmem] with p hp
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using inCoordinates_mpullback_family (I := I) (φ p) f g p₀ p hp

end Family

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Pulling back along a map `f` the rough form on `N × M` whose value at `(t, y)` is the pullback
of `β t` along the projection to `M` gives, at `x`, the pullback of `β (f x).1` along the second
component of `f`. -/
theorem mpullback_fun_mpullback_snd_apply {EX HX X : Type*} [NormedAddCommGroup EX]
    [NormedSpace ℝ EX] [TopologicalSpace HX] [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners ℝ EX HX} (β : N → RoughForm I M F k) {f : X → N × M} {x : X}
    (hf : MDifferentiableAt IX (J.prod I) f x) :
    mpullback IX (J.prod I) f (fun p ↦ mpullback (J.prod I) I Prod.snd (β p.1) p) x =
      mpullback IX I (Prod.snd ∘ f) (β (f x).1) x := by
  rw [mpullback_comp_at hf mdifferentiableAt_snd]
  -- Both sides only read the value at `f x` of the form on `N × M`.
  ext v
  simp only [mpullback_apply]

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- The rough form on `N × M` whose value at `(t, y)` is the pullback of `β t` along the
projection to `M` has the slice `β t` at `t`. -/
theorem mpullback_prodMk_fun_mpullback_snd_apply (β : N → RoughForm I M F k) (t : N) (x : M) :
    mpullback I (J.prod I) (Prod.mk t)
        (fun p ↦ mpullback (J.prod I) I Prod.snd (β p.1) p) x = β t x := by
  rw [mpullback_fun_mpullback_snd_apply β (f := Prod.mk t)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id),
    Prod.snd_comp_mk, mpullback_id]

/-- **Forms with prescribed slices.** For a family `β` of rough forms on `M` over `N`, the rough
form on `N × M` whose value at `(t, y)` is the pullback of `β t` along the projection to `M` is
`C^m` at `p` exactly when the slice section `(t, y) ↦ β t y`, along the projection, is. -/
theorem contMDiffAt_fun_mpullback_snd_iff {m : WithTop ℕ∞} (β : N → RoughForm I M F k)
    (p : N × M) :
    ContMDiffAt (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) m
        (fun q ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) q
          (mpullback (J.prod I) I Prod.snd (β q.1) q)) p ↔
      ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun q : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
          (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) q.2
          (β q.1 q.2)) p := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := ContMDiffAt.mpullback_form_family (hφ := h) (f := fun q : N × M ↦ Prod.mk q.1)
      (g := Prod.snd) (n := ω) (p₀ := p)
      ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt contMDiffAt_snd le_top
    simpa only [mpullback_prodMk_fun_mpullback_snd_apply] using this
  · exact ContMDiffAt.mpullback_form_family_of_family (φ := fun q : N × M ↦ β q.1)
      (f := fun _ ↦ Prod.snd) (g := id) (n := ω) h
      (contMDiff_snd.comp contMDiff_snd).contMDiffAt contMDiffAt_id le_top

/-- **Slice sections are local in `M`.** For a family `β` of rough forms on an open subset `W`
of `M` and an open subset `U ≤ W`, the slice section of the restrictions of the `β t` to `U` is
`C^m` at `(t, x)` exactly when the slice section of `β` is `C^m` at `(t, x)`. -/
theorem contMDiffAt_mpullback_inclusion_iff_of_family {m : WithTop ℕ∞} {U W : Opens M}
    (h : U ≤ W) (β : N → RoughForm I W F k) (p : N × U) :
    ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun q : N × U ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
          (E := fun y : U ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial U F y) q.2
          (mpullback I I (Opens.inclusion h) (β q.1) q.2)) p ↔
      ContMDiffAt (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
        (fun q : N × W ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
          (E := fun y : W ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial W F y) q.2 (β q.1 q.2))
        (p.1, Opens.inclusion h p.2) := by
  have hf : IsLocalDiffeomorphAt (J.prod I) (J.prod I) ω (Prod.map id (Opens.inclusion h)) p :=
    (isLocalDiffeomorph_id p.1).prodMap (isLocalDiffeomorph_inclusion h p.2)
  rw [← contMDiffAt_fun_mpullback_snd_iff,
    ← contMDiffAt_fun_mpullback_snd_iff (fun t ↦ mpullback I I (Opens.inclusion h) (β t))]
  refine Iff.trans (Iff.of_eq (congrArg (ContMDiffAt _ _ _ · p) (funext fun q ↦ ?_)))
    (hf.contMDiffAt_mpullback_form_iff le_top)
  have hq : MDifferentiableAt (J.prod I) (J.prod I) (Prod.map id (Opens.inclusion h)) q :=
    mdifferentiableAt_id.prodMap ((contMDiff_inclusion h).mdifferentiableAt (n := 1) one_ne_zero)
  rw [mpullback_fun_mpullback_snd_apply _ hq, Prod.map_snd',
    mpullback_comp_at mdifferentiableAt_snd
      ((contMDiff_inclusion h).mdifferentiableAt (n := 1) one_ne_zero), Prod.map_fst, id_eq]

end TauCeti

namespace TauCeti.SmoothForm

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **The form on `N × M` with prescribed slices.** For a family `α` of smooth forms on `M`
over `N` whose slice section `(t, y) ↦ (α t) y`, along the projection to `M`, is smooth, the
smooth form on `N × M` whose value at `(t, y)` is the pullback of `α t` along the projection to
`M`. It vanishes on the directions of `N` (`TauCeti.SmoothForm.ofSlices_apply`), and its slice at
`t` is `α t`
(`TauCeti.SmoothForm.mpullback_prodMk_ofSlices`). -/
def ofSlices (α : N → SmoothForm I M F k)
    (hα : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((α p.1).val p.2))) :
    SmoothForm (J.prod I) (N × M) F k :=
  ⟨fun p ↦ TauCeti.mpullback (J.prod I) I Prod.snd (α p.1).val p,
    IsSmoothForm.mem_smoothBundleForms <| (isSmoothForm_def _ _).mpr fun p ↦
      (contMDiffAt_fun_mpullback_snd_iff (fun t ↦ (α t).val) p).mpr (hα p)⟩

variable {α : N → SmoothForm I M F k}
  {hα : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
    (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
      (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((α p.1).val p.2))}

/-- The value of `TauCeti.SmoothForm.ofSlices α hα` at `(t, y)` is the pullback of `α t` along
the projection to `M`. -/
theorem coe_ofSlices :
    (ofSlices α hα).val = fun p ↦ TauCeti.mpullback (J.prod I) I Prod.snd (α p.1).val p :=
  (rfl)

/-- The form `TauCeti.SmoothForm.ofSlices α hα` evaluates `α t` on the components along `M` of
the tangent vectors at `(t, y)`. -/
theorem ofSlices_apply (p : N × M) (v : Fin k → TangentSpace (J.prod I) p) :
    (ofSlices α hα).val p v =
      (α p.1).val p.2 (fun i ↦ (Manifold.tangentSpaceProdEquiv p (v i)).2) := by
  rw [coe_ofSlices, ← mpullback_snd_apply (I := J) (α p.1) p v, coe_mpullback]

/-- The slice at `t` of `TauCeti.SmoothForm.ofSlices α hα` is `α t`. -/
@[simp]
theorem mpullback_prodMk_ofSlices (t : N) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (ofSlices α hα) = α t :=
  Subtype.ext <| funext fun x ↦ by
    rw [coe_mpullback, coe_ofSlices]
    exact mpullback_prodMk_fun_mpullback_snd_apply (fun t ↦ (α t).val) t x

/-- The slice at `t` of the pullback of a form `α` on `M` along the projection `N × M → M` is
`α`. -/
@[simp]
theorem mpullback_prodMk_mpullback_snd (t : N) (α : SmoothForm I M F k) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
      (mpullback Prod.snd contMDiff_snd α : SmoothForm (J.prod I) (N × M) F k) = α :=
  (mpullback_mpullback (Prod.mk t) Prod.snd (I' := J.prod I)
    (contMDiff_const.prodMk contMDiff_id) contMDiff_snd α).trans
      (LinearMap.congr_fun mpullback_id α)

/-- **The two orders of a cylinder.** The slice at `t` of the pullback of a form `Ω` on `M × N`
along the swap `N × M → M × N` is the pullback of `Ω` along `x ↦ (x, t)`. -/
theorem mpullback_prodMk_mpullback_prodComm (Ω : SmoothForm (I.prod J) (M × N) F k) (t : N) :
    mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (mpullback (Diffeomorph.prodComm J I N M ∞) (Diffeomorph.prodComm J I N M ∞).contMDiff
          Ω) =
      mpullback (fun x ↦ (x, t)) (contMDiff_id.prodMk contMDiff_const) Ω := by
  have hcomp :
      (Diffeomorph.prodComm J I N M ∞ ∘ Prod.mk t : M → M × N) = fun x ↦ (x, t) := by
    rw [Diffeomorph.coe_prodComm]
    rfl
  simp only [mpullback_mpullback, hcomp]

end TauCeti.SmoothForm

namespace SymplecticGeometry

open TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable (J) in
/-- **Smooth families of forms.** A family `α` of smooth `k`-forms on `M`, indexed by the points
of a manifold `N`, is smooth when it is the family of slices of a smooth form `Ω` on `N × M`:
`α t` is the pullback of `Ω` along the inclusion `y ↦ (t, y)`. -/
def IsSmoothFamily (α : N → SmoothForm I M F k) : Prop :=
  ∃ Ω : SmoothForm (J.prod I) (N × M) F k, ∀ t,
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = α t

/-- The defining property of `SymplecticGeometry.IsSmoothFamily`. -/
theorem isSmoothFamily_def {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔ ∃ Ω : SmoothForm (J.prod I) (N × M) F k, ∀ t,
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω = α t :=
  Iff.rfl

/-- **Smooth families are those with a smooth slice section.** A family `α` of smooth forms on
`M` over `N` is smooth exactly when `(t, y) ↦ (α t) y` is a smooth section along the projection
`N × M → M`. -/
theorem isSmoothFamily_iff_contMDiff {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔ ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((α p.1).val p.2)) := by
  refine ⟨?_, fun h ↦ ⟨SmoothForm.ofSlices α h, SmoothForm.mpullback_prodMk_ofSlices⟩⟩
  rintro ⟨Ω, hΩ⟩
  simp_rw [← hΩ, SmoothForm.coe_mpullback]
  exact contMDiff_mpullback_prodMk_form Ω.contMDiff

/-- A family `α` of smooth forms on `M` over `N` is smooth exactly when the rough form on `N × M`
whose value at `(t, y)` is the pullback of `α t` along the projection to `M` is smooth. -/
theorem isSmoothFamily_iff_isSmoothForm {α : N → SmoothForm I M F k} :
    IsSmoothFamily J α ↔
      IsSmoothForm (J.prod I) ∞
        fun p ↦ TauCeti.mpullback (J.prod I) I Prod.snd (α p.1).val p := by
  rw [isSmoothFamily_iff_contMDiff, isSmoothForm_def]
  exact forall_congr' fun p ↦ (contMDiffAt_fun_mpullback_snd_iff (fun t ↦ (α t).val) p).symm

namespace IsSmoothFamily

variable {α β : N → SmoothForm I M F k}

/-- The values of a smooth family at a point `x` on fixed tangent vectors depend smoothly on the
parameter. -/
theorem contMDiff_apply (h : IsSmoothFamily J α) (x : M) (v : Fin k → TangentSpace I x) :
    ContMDiff J 𝓘(ℝ, F) ∞ (fun t ↦ (α t).val x v) := by
  have hS := (isSmoothFamily_iff_contMDiff.mp h).comp
    (contMDiff_id.prodMk contMDiff_const : ContMDiff J (J.prod I) ∞ fun t ↦ (t, x))
  intro t
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp (hS t)).2
  simp only [Function.comp_apply, id_eq,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd] at hc
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have := ((ContinuousAlternatingMap.apply ℝ E F
    fun i ↦ (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (v i)
      ).contMDiff.contMDiffAt).comp t hc
  simpa only [Function.comp_def, ContinuousAlternatingMap.apply_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx] using this

/-- Two smooth families of forms that agree at the parameters of a dense set are equal. -/
theorem ext_on (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) {s : Set N} (hs : Dense s)
    (h : EqOn α β s) : α = β := by
  funext t
  ext x v
  exact congrFun (Continuous.ext_on hs (hα.contMDiff_apply x v).continuous
    (hβ.contMDiff_apply x v).continuous fun r hr ↦ by rw [h hr]) t

/-- The sum of two smooth families is smooth. -/
protected theorem add (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) :
    IsSmoothFamily J (fun t ↦ α t + β t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  obtain ⟨Θ, hΘ⟩ := hβ
  exact ⟨Ω + Θ, fun t ↦ by rw [map_add, hΩ, hΘ]⟩

/-- The negative of a smooth family is smooth. -/
protected theorem neg (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ -α t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨-Ω, fun t ↦ by rw [map_neg, hΩ]⟩

/-- The difference of two smooth families is smooth. -/
protected theorem sub (hα : IsSmoothFamily J α) (hβ : IsSmoothFamily J β) :
    IsSmoothFamily J (fun t ↦ α t - β t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  obtain ⟨Θ, hΘ⟩ := hβ
  exact ⟨Ω - Θ, fun t ↦ by rw [map_sub, hΩ, hΘ]⟩

/-- A constant multiple of a smooth family is smooth. -/
protected theorem smul (hα : IsSmoothFamily J α) (c : ℝ) :
    IsSmoothFamily J (fun t ↦ c • α t) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨c • Ω, fun t ↦ by rw [map_smul, hΩ]⟩

/-- The product of a smooth family with a smooth function of the parameter is smooth. -/
protected theorem fun_smul (hα : IsSmoothFamily J α) {c : N → ℝ}
    (hc : ContMDiff J 𝓘(ℝ) ∞ c) :
    IsSmoothFamily J (fun t ↦ c t • α t) := by
  rw [isSmoothFamily_iff_isSmoothForm] at hα ⊢
  simp only [Submodule.coe_smul, mpullback_smul, Pi.smul_apply]
  exact hα.fun_smul (hc.comp contMDiff_fst)

/-- The product of a smooth family with a fixed smooth function on `M` is smooth. -/
protected theorem funSMul (hα : IsSmoothFamily J α) (g : C^∞⟮I, M; ℝ⟯) :
    IsSmoothFamily J (fun t ↦ SmoothForm.funSMulₗ g (α t)) := by
  rw [isSmoothFamily_iff_isSmoothForm] at hα ⊢
  simp only [SmoothForm.coe_funSMulₗ, mpullback_fun_smul]
  exact hα.fun_smul (g.contMDiff.comp contMDiff_snd)

end IsSmoothFamily

/-- A constant family is smooth: it is the family of slices of the pullback of its value along
the projection `N × M → M`. -/
theorem isSmoothFamily_const (α : SmoothForm I M F k) : IsSmoothFamily J (fun _ : N ↦ α) :=
  ⟨_, fun t ↦ SmoothForm.mpullback_prodMk_mpullback_snd t α⟩

/-- The slices `t ↦ Ω (t, ·)` of a smooth form `Ω` on `N × M` form a smooth family. -/
theorem isSmoothFamily_mpullback_prodMk (Ω : SmoothForm (J.prod I) (N × M) F k) :
    IsSmoothFamily J fun t ↦
      SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) Ω :=
  ⟨Ω, fun _ ↦ rfl⟩

namespace IsSmoothFamily

/-- A finite sum of smooth families is smooth. -/
protected theorem sum {ι : Type*} {s : Finset ι} {α : ι → N → SmoothForm I M F k}
    (hα : ∀ i ∈ s, IsSmoothFamily J (α i)) :
    IsSmoothFamily J (fun t ↦ ∑ i ∈ s, α i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isSmoothFamily_const (J := J) (N := N) 0
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hα i (Finset.mem_insert_self i s)).add
      (ih fun j hj ↦ hα j (Finset.mem_insert_of_mem hj))

/-- The exterior derivatives of a smooth family form a smooth family. -/
protected theorem mextDeriv [IsManifold I 2 M] [IsManifold J 2 N] {α : N → SmoothForm I M F k}
    (hα : IsSmoothFamily J α) : IsSmoothFamily J (fun t ↦ mextDerivₗ I k (α t)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  exact ⟨mextDerivₗ (J.prod I) k Ω, fun t ↦ by
    dsimp only
    rw [← SmoothForm.mextDerivₗ_mpullback, hΩ]⟩

section Maps

variable {E' H' M' EN' HN' N' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'} [IsManifold I' 1 M']
  [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  [TopologicalSpace N'] [ChartedSpace HN' N'] {J' : ModelWithCorners ℝ EN' HN'}
  [IsManifold J' 1 N'] {α : N → SmoothForm I M F k}

/-- **Pullback of a smooth family along a smooth family of maps.** For a smooth map
`f : N × M' → M`, the pullbacks of `α t` along the slices `f (t, ·)` form a smooth family. -/
protected theorem mpullback_family (hα : IsSmoothFamily J α) {f : N × M' → M}
    (hf : ContMDiff (J.prod I') I ∞ f) :
    IsSmoothFamily J (fun t ↦ SmoothForm.mpullback (fun x ↦ f (t, x))
      (hf.comp (contMDiff_const.prodMk contMDiff_id)) (α t)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  refine ⟨SmoothForm.mpullback (fun p ↦ (p.1, f p)) (contMDiff_fst.prodMk hf) Ω, fun t ↦ ?_⟩
  have hcomp : ((fun p ↦ (p.1, f p)) ∘ Prod.mk t : M' → N × M) =
      Prod.mk t ∘ fun x ↦ f (t, x) := rfl
  simp only [← hΩ, SmoothForm.mpullback_mpullback, hcomp]

/-- The pullbacks of a smooth family along a smooth map form a smooth family. -/
protected theorem mpullback (hα : IsSmoothFamily J α) (f : M' → M) (hf : ContMDiff I' I ∞ f) :
    IsSmoothFamily J (fun t ↦ SmoothForm.mpullback f hf (α t)) :=
  hα.mpullback_family (f := fun p : N × M' ↦ f p.2) (hf.comp contMDiff_snd)

/-- Reparametrizing a smooth family by a smooth map of parameter manifolds gives a smooth
family. -/
protected theorem comp (hα : IsSmoothFamily J α) (φ : N' → N) (hφ : ContMDiff J' J ∞ φ) :
    IsSmoothFamily J' (fun s ↦ α (φ s)) := by
  obtain ⟨Ω, hΩ⟩ := hα
  refine ⟨SmoothForm.mpullback (Prod.map φ id) (hφ.prodMap contMDiff_id) Ω, fun s ↦ ?_⟩
  have hcomp : (Prod.map φ id ∘ Prod.mk s : M → N × M) = Prod.mk (φ s) := rfl
  simp only [← hΩ, SmoothForm.mpullback_mpullback, hcomp]

end Maps

/-- **Cut-off and extension by zero of a smooth family.** Let `α` be a smooth family of forms on
an open subset `U ≤ W`, and `g` a smooth function on `W` vanishing near every point of `W` outside
`U`. A family `β` of smooth forms on `W` whose value at `t` is the extension by zero of
`g • α t` is smooth. -/
protected theorem extendByZero_smul {U W : Opens M} (h : U ≤ W)
    {α : N → SmoothForm I U F k} (hα : IsSmoothFamily J α) {g : W → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hzero : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, g y = 0)
    {β : N → SmoothForm I W F k}
    (hβ : ∀ t, (β t).val =
      RoughForm.extendByZero W fun y : U ↦ g (Opens.inclusion h y) • (α t).val y) :
    IsSmoothFamily J β := by
  rw [isSmoothFamily_iff_contMDiff]
  rintro ⟨t, x⟩
  by_cases hx : (x : M) ∈ U
  · -- Near `x`, the restriction of `β` to `U` is the smooth family `g • α`.
    have hgα :=
      (isSmoothFamily_iff_isSmoothForm.mp hα).fun_smul
        (f := fun q : N × U ↦ g (Opens.inclusion h q.2))
        ((hg.comp (contMDiff_inclusion h)).comp contMDiff_snd)
    refine (contMDiffAt_mpullback_inclusion_iff_of_family h (fun s ↦ (β s).val)
      (t, ⟨x, hx⟩)).mp ?_
    simp only [hβ, RoughForm.mpullback_inclusion_extendByZero]
    refine (contMDiffAt_fun_mpullback_snd_iff
      (fun s y ↦ g (Opens.inclusion h y) • (α s).val y) _).mp ?_
    simpa only [mpullback_fun_smul] using hgα.contMDiff (t, ⟨x, hx⟩)
  · -- Near `x`, every `β s` vanishes.
    have hev : ∀ᶠ q : N × W in 𝓝 (t, x), ∀ s, (β s).val q.2 = 0 := by
      have hy : ∀ᶠ y in 𝓝 x, ∀ s, (β s).val y = 0 := by
        filter_upwards [(hzero x hx).eventually_nhds] with y hy s
        rw [hβ]
        exact (RoughForm.eventually_extendByZero_smul_eq_zero h (α s).val hy).self_of_nhds
      exact (continuous_snd.tendsto (t, x)).eventually hy
    refine ((contMDiff_zeroSection ℝ (fun y : W ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F)).comp
      contMDiff_snd (t, x)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    rw [hq q.1]
    -- The zero section takes the value `0` at every point.
    rfl

end IsSmoothFamily

/-- **Smoothness of families is local.** A family of forms on `U ⊔ V` is smooth exactly when its
restrictions to `U` and to `V` are. -/
theorem isSmoothFamily_iff_mpullback_inclusion_sup {U V : Opens M}
    {α : N → SmoothForm I (U ⊔ V : Opens M) F k} :
    IsSmoothFamily J α ↔
      IsSmoothFamily J (fun t ↦
        SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) (α t)) ∧
      IsSmoothFamily J (fun t ↦
        SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) (α t)) := by
  refine ⟨fun h ↦ ⟨h.mpullback _ _, h.mpullback _ _⟩, fun ⟨hU, hV⟩ ↦ ?_⟩
  rw [isSmoothFamily_iff_contMDiff] at hU hV ⊢
  rintro ⟨t, x⟩
  rcases Opens.mem_sup.mp x.property with hx | hx
  · exact (contMDiffAt_mpullback_inclusion_iff_of_family le_sup_left (fun s ↦ (α s).val)
      (t, ⟨x, hx⟩)).mp
        (by simpa only [SmoothForm.coe_mpullback] using hU (t, ⟨x, hx⟩))
  · exact (contMDiffAt_mpullback_inclusion_iff_of_family le_sup_right (fun s ↦ (α s).val)
      (t, ⟨x, hx⟩)).mp
        (by simpa only [SmoothForm.coe_mpullback] using hV (t, ⟨x, hx⟩))

section Interior

variable {E H M EN HN N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN} [IsManifold J 1 N]

/-- For a jointly smooth family `X_t`, `t ∈ N`, of vector fields, the contractions `ι_{X_t} σ` of
a two-form `σ` form a smooth family of one-forms. -/
theorem isSmoothFamily_interiorₗ (σ : SmoothTwoForm I M)
    {X : N → Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯}
    (hX : ContMDiff (J.prod I) I.tangent ∞
      fun p : N × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) :
    IsSmoothFamily J fun t ↦ σ.interiorₗ (X t) := by
  rw [isSmoothFamily_iff_contMDiff]
  intro p
  rw [← SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
    (α := fun q : N × M ↦ σ.interiorₗ (X q.1))]
  simp only [SmoothTwoForm.degreeOneEquiv_interiorₗ]
  exact ((σ.contMDiff_flat.comp contMDiff_snd).clm_bundle_apply hX) p

end Interior

end SymplecticGeometry
