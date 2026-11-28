/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.LocalForm
import SymplecticGeometry.Geometry.Manifold.DeRham.FamilyPrimitive
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Interior
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.ParameterProduct
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic

/-!
# Closed forms over a patch with given fibre and mixed components

Let `τ` be a smooth two-form on `EB × F`, in the setting of `Fibration/LocalForm.lean`: `EB` is a
real Banach space with a basis `bs`, and `τ` has the mixed components `αᵢ(x)` and the base
components `f_{ij}(x)`, families of one-forms and functions on `F` indexed by `x ∈ EB`. This file
constructs a closed two-form over a patch `U ×ˢ univ` of `EB × F` with the same fibre and mixed
components as `τ`, the local step of the existence of the coupling form of a symplectic
connection with Hamiltonian curvature ([McDuffSalamon2017], §6.4, proof of Theorem 6.4.1).

The first step chooses primitives of the curls `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` of the mixed components
smoothly in `x`, where `∂ᵢ` differentiates along `bs i`. If, at every `x` of an open
set `U`, the curl is the differential of a smooth function on `F`, then there is a function `f`
on `EB × F`, smooth on `U ×ˢ univ` and vanishing on `U × {y₀}`, whose restriction to each fibre
over `x ∈ U` is such a primitive
(`TauCeti.SmoothTwoForm.exists_contMDiffOn_mvfderiv_eq_mixedCurl`). The second step replaces the
base components of `τ` by these primitives, which gives a form whose exterior derivative
vanishes over the patch when `τ` is vertically closed there and `F` is connected
(`TauCeti.SmoothTwoForm.exists_isClosed_local`).

## Main results

* `TauCeti.SmoothTwoForm.exists_contMDiffOn_mvfderiv_eq_mixedCurl`: jointly smooth
  primitives of the mixed curls over an open patch, normalized at a point `y₀` of `F`.
* `TauCeti.SmoothTwoForm.exists_isClosed_local`: a two-form, smooth and closed over the patch,
  that agrees with `τ` whenever one of the two vectors is tangent to the fibre.
* `ContinuousAlternatingMap.apply_vecCons_inl_eq_zero_of_basis` and
  `ContinuousAlternatingMap.apply_vecCons_inl_inl_inr_eq_zero_of_basis`: forms on a product
  `M₁ × M₂` that vanish on the vectors of a basis of `M₁` vanish on all vectors of `M₁`.
* `Module.Basis.mpullback_fst_wedge_coordOneForm_apply`: the values of `pr₁^*(dxᵢ ∧ dxⱼ)`.

## Implementation notes

By the formula for the curl in `Fibration/LocalForm.lean`
(`TauCeti.SmoothTwoForm.mixedCurl_eq_mvfderiv_baseComponent_sub_mextDeriv`), the curl at `x` is
`d_F f_{ij}(x)` minus the slice over `x` of the smooth one-form `η = ι(∂ⱼ, 0) ι(∂ᵢ, 0) dτ` on
`EB × F`. If the curl at `x` is exact, then so is that slice.
The slices of `η` over the patch, the subtype of `U` as an open subset of `EB`, form a smooth
family of exact one-forms on `F`, so the library's
`SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms` gives them jointly
smooth primitives `h`. Then `f_{ij} - h`, extended by zero off the patch, has the curls as fibre
differentials, and subtracting its values at `y₀` normalizes it. Smoothness on `U ×ˢ univ` comes
from that of `h` on `U × F` by `ContMDiff.contMDiffOn_opens_prod_of_eq`.

The form of `TauCeti.SmoothTwoForm.exists_isClosed_local` is
`φ = τ + ∑_{i<j} (f_{ij} - τ((∂ᵢ, 0), (∂ⱼ, 0))) • pr₁^*(dxᵢ ∧ dxⱼ)`. The pull-backs
`pr₁^*(dxᵢ ∧ dxⱼ)` vanish as soon as one vector is vertical, so `φ` agrees with `τ` there, and
its base components are the `f_{ij}`. Closedness is checked on three kinds of triples
(`ContinuousAlternatingMap.eq_zero_of_forall_prod_fin_three`). On two fibre vectors, `dφ` only
depends on the fibre and mixed components
(`TauCeti.RoughForm.mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum`), so it is `dτ` there,
which vanishes. On `(∂ᵢ, 0), (∂ⱼ, 0), (0, w)`, the formula
`TauCeti.RoughForm.mextDeriv_prod_apply_snoc_inr`, for `φ` and for `τ`, together with the formula
for the curl, gives `d_F f_{ij}(x)(w)` minus the curl, which is zero by the choice of `f_{ij}`.
On three base vectors, `TauCeti.RoughForm.mextDeriv_prod_apply_inl_eq_zero` concludes, since the
base components of `φ` vanish at `y₀`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.4 (proof of Theorem 6.4.1), with [McDuffSalamon2019Errata].
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace ContinuousAlternatingMap

variable {ι M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module ℝ M₂] [TopologicalSpace M₂] [Finite ι] [LinearOrder ι]

/-- A two-form `S` on `M₁ × M₂` vanishes on all pairs of vectors of `M₁` once it vanishes on the
pairs `(bs i, 0), (bs j, 0)` with `i < j` of a basis `bs` of `M₁`. -/
theorem apply_vecCons_inl_eq_zero_of_basis (bs : Module.Basis ι ℝ M₁)
    (S : (M₁ × M₂) [⋀^Fin 2]→L[ℝ] ℝ) (h : ∀ i j, i < j → S ![(bs i, 0), (bs j, 0)] = 0)
    (a b : M₁) : S ![(a, 0), (b, 0)] = 0 := by
  have := Fintype.ofFinite ι
  rw [S.apply_vecCons_prod_eq_sum bs]
  have h0 (u : M₁ × M₂) : S ![0, u] = 0 := S.map_coord_zero 0 rfl
  simp only [Prod.mk_zero_zero, h0, smul_zero, sub_self, Finset.sum_const_zero, zero_add]
  exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j hj ↦ by
    rw [h i j (Finset.mem_filter.1 hj).2, smul_zero]

/-- A three-form `T` on `M₁ × M₂` vanishes on all triples `(a, 0), (b, 0), (0, w)` once it
vanishes on the triples `(bs i, 0), (bs j, 0), (0, w)` with `i < j` of a basis `bs` of `M₁`. -/
theorem apply_vecCons_inl_inl_inr_eq_zero_of_basis (bs : Module.Basis ι ℝ M₁)
    (T : (M₁ × M₂) [⋀^Fin 3]→L[ℝ] ℝ) (w : M₂)
    (h : ∀ i j, i < j → T ![(bs i, 0), (bs j, 0), (0, w)] = 0) (a b : M₁) :
    T ![(a, 0), (b, 0), (0, w)] = 0 := by
  rw [← T.map_vecCons_rotate, ← curryLeftTopological_apply_apply]
  refine apply_vecCons_inl_eq_zero_of_basis bs _ (fun i j hij ↦ ?_) a b
  rw [curryLeftTopological_apply_apply, T.map_vecCons_rotate]
  exact h i j hij

end ContinuousAlternatingMap

namespace Module.Basis

variable {ι M : Type*} [AddCommGroup M] [Module ℝ M] [Fintype ι] [LinearOrder ι]

/-- The coefficients `c k l`, `k < l`, of a two-form `∑_{k<l} c k l dxₖ ∧ dxₗ` in the coordinates
of a basis `bs` are its values on `bs i, bs j`. -/
theorem sum_sum_mul_coord_mul_sub_coord_mul (bs : Module.Basis ι ℝ M) (c : ι → ι → ℝ)
    {i j : ι} (hij : i < j) :
    ∑ k, ∑ l with k < l, c k l * (bs.coord k (bs i) * bs.coord l (bs j) -
      bs.coord k (bs j) * bs.coord l (bs i)) = c i j := by
  classical
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i (fun k _ hk ↦ Finset.sum_eq_zero fun l hl ↦ ?_) (by simp),
    Finset.sum_eq_single j (fun l _ hl ↦ ?_) (by simp [hij])]
  · simp [hij.ne, hij.ne']
  · grind
  · grind

omit [Fintype ι] [LinearOrder ι] in
/-- The pull-back to `E × F` of the wedge `dxᵢ ∧ dxⱼ` of two coordinate one-forms of a basis
`bs` of `E` takes the value `xᵢ(v₁) xⱼ(w₁) - xᵢ(w₁) xⱼ(v₁)` on `(v₁, v₂), (w₁, w₂)`. -/
theorem mpullback_fst_wedge_coordOneForm_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (bs : Module.Basis ι ℝ E)
    {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
    {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
    (i j : ι) (z : E × F) (v w : TangentSpace (𝓘(ℝ, E).prod IF) z) :
    (TauCeti.SmoothForm.mpullback Prod.fst contMDiff_fst
      (TauCeti.SmoothForm.wedge (bs.coordOneForm i) (bs.coordOneForm j))).val z ![v, w] =
      bs.coord i v.1 * bs.coord j w.1 - bs.coord i w.1 * bs.coord j v.1 := by
  rw [TauCeti.SmoothForm.mpullback_wedge, TauCeti.SmoothForm.wedge_apply_one_one]
  simp
  rfl

end Module.Basis

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
  {ι : Type*} (τ : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F)) (bs : Module.Basis ι ℝ EB)

open SymplecticGeometry in
/-- The slices of the one-form `ι(bs j, 0) ι(bs i, 0) dτ` on `EB × F`: on a vector `w` tangent
to `F`, the slice over `x` takes the value of `dτ` on `(bs i, 0), (bs j, 0), (0, w)`. -/
private theorem exists_mpullback_prodMk_apply_eq_mextDeriv (i j : ι) :
    ∃ η : SmoothForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 1, ∀ (x : EB) (y : F) (w : TangentSpace IF y),
      (SmoothForm.mpullback (Prod.mk x) (contMDiff_const.prodMk contMDiff_id) η).val y ![w] =
        mextDeriv τ.val (x, y) ![(bs i, 0), (bs j, 0), ((0 : EB), w)] := by
  refine ⟨SmoothForm.interiorProduct (baseField bs j)
    (SmoothForm.interiorProduct (baseField bs i) (mextDerivₗ _ 2 τ)), fun x y w ↦ ?_⟩
  rw [SmoothForm.mpullback_apply_one, mfderiv_prodMk_right_apply, SmoothForm.coe_interiorProduct,
    RoughForm.interior_apply, SmoothForm.coe_interiorProduct, RoughForm.interior_apply,
    mextDerivₗ_apply, baseField_apply, baseField_apply]
  -- The vector `(0, w)` lies in the tangent space of `EB × F`, which is `EB × EF` by definition.
  rfl

variable [CompleteSpace EB] [CompleteSpace EF]

/-- **Smooth primitives of the curls of the mixed components.** Let `τ` be a smooth two-form on
`EB × F` with mixed components `αₖ` for the basis `bs`, and `U` an open set of `EB`. If, at every
`x ∈ U`, the one-form `∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F` is the differential of a smooth function, then
for every `y₀ : F` there is a function `f` on `EB × F`, smooth on `U ×ˢ univ`, with
`f (x, y₀) = 0` for `x ∈ U`, whose restriction to the fibre over each `x ∈ U` has differential
`∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)`. Here `∂ₖ` differentiates in `x` along `bs k`. -/
theorem exists_contMDiffOn_mvfderiv_eq_mixedCurl {U : Set EB} (hU : IsOpen U) {i j : ι}
    (h : ∀ x ∈ U, ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
      mvfderiv IF g y w = RoughForm.mixedCurl τ.val bs i j x y w)
    (y₀ : F) :
    ∃ f : EB × F → ℝ, ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ f (U ×ˢ univ) ∧
      (∀ x ∈ U, f (x, y₀) = 0) ∧ ∀ x ∈ U, ∀ (y : F) (w : TangentSpace IF y),
        mvfderiv IF (fun y ↦ f (x, y)) y w = RoughForm.mixedCurl τ.val bs i j x y w := by
  classical
  let V : TopologicalSpace.Opens EB := ⟨U, hU⟩
  obtain ⟨η, hη⟩ := exists_mpullback_prodMk_apply_eq_mextDeriv τ bs i j
  -- The slices of `η` over the patch form a smooth family of one-forms on `F`.
  let α : V → SmoothForm IF F ℝ 1 := fun t ↦
    SmoothForm.mpullback (Prod.mk (t : EB)) (contMDiff_const.prodMk contMDiff_id) η
  have hα : SymplecticGeometry.IsSmoothFamily 𝓘(ℝ, EB) α :=
    (SymplecticGeometry.isSmoothFamily_mpullback_prodMk η).comp _ contMDiff_subtypeVal
  have hf := contMDiff_baseComponent τ bs i j
  have hfx (x : EB) : ContMDiff IF 𝓘(ℝ) ∞ (RoughForm.baseComponent τ.val bs i j x) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  -- Each `α t` is the differential of `f_{ij}(t) - g` for a primitive `g` of the curl at `t`.
  have hex (t : V) : α t ∈ exactForms IF F 1 := by
    obtain ⟨g, hg, hdg⟩ := h t t.property
    rw [exactForms_succ, LinearMap.mem_range]
    refine ⟨⟨RoughForm.ofFunction IF _,
      (isSmoothForm_ofFunction_iff.2 ((hfx t).sub hg)).mem_smoothBundleForms⟩, Subtype.ext ?_⟩
    rw [mextDerivₗ_apply]
    funext y
    rw [mextDeriv_ofFunction]
    ext v
    rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, show v = ![v 0] from
      funext fun k ↦ by fin_cases k; rfl, hη, mvfderiv_fun_sub
      ((hfx t).mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp)), sub_apply, hdg,
      mixedCurl_eq_mvfderiv_baseComponent_sub_mextDeriv]
    abel
  obtain ⟨h₀, hh₀, hdh₀⟩ :=
    SymplecticGeometry.exists_contMDiff_mextDeriv_eq_of_forall_mem_exactForms hα hex
  -- The primitives `h₀ (t, ·)` of the `α t`, extended by zero off the patch.
  let H : EB × F → ℝ := fun p ↦ if hp : p.1 ∈ U then h₀ (⟨p.1, hp⟩, p.2) else 0
  have hH {x : EB} (hx : x ∈ U) (y : F) : H (x, y) = h₀ (⟨x, hx⟩, y) := by simp [H, hx]
  have hHs : ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ H (U ×ˢ univ) :=
    hh₀.contMDiffOn_opens_prod_of_eq (U := V) fun x hx y ↦ hH hx y
  let f₀ : EB × F → ℝ := fun p ↦ RoughForm.baseComponent τ.val bs i j p.1 p.2 - H p
  have hf₀ : ContMDiffOn (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ f₀ (U ×ˢ univ) := hf.contMDiffOn.sub hHs
  refine ⟨fun p ↦ f₀ p - f₀ (p.1, y₀), hf₀.sub (hf₀.comp
    (contMDiff_fst.prodMk contMDiff_const).contMDiffOn fun p hp ↦ ⟨hp.1, mem_univ _⟩),
    fun x _ ↦ sub_self _, fun x hx y w ↦ ?_⟩
  let t : V := ⟨x, hx⟩
  have hh : ContMDiff IF 𝓘(ℝ) ∞ fun y ↦ h₀ (t, y) :=
    hh₀.comp (contMDiff_const.prodMk contMDiff_id)
  have he : (fun y ↦ f₀ (x, y) - f₀ (x, y₀)) =
      fun y ↦ (RoughForm.baseComponent τ.val bs i j x y - h₀ (t, y)) - f₀ (x, y₀) :=
    funext fun y ↦ by simp only [f₀, hH hx y, t]
  have hd : mvfderiv IF (fun y ↦ h₀ (t, y)) y w = (α t).val y ![w] := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← mextDeriv_ofFunction_apply, hdh₀ t]
  rw [he, mvfderiv_fun_sub (((hfx x).sub hh).mdifferentiableAt (by simp))
      mdifferentiableAt_const, mvfderiv_const, sub_zero, mvfderiv_fun_sub
      ((hfx x).mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp)), sub_apply, hd, hη,
    mixedCurl_eq_mvfderiv_baseComponent_sub_mextDeriv]


/-- **A closed form over a patch with the fibre and mixed components of `τ`.** Let `τ` be a
smooth two-form on `EB × F`, with `F` connected, and `U` an open set of `EB` over which `τ` is
vertically closed for the first projection. If, at every `x ∈ U` and for all `i j`, the one-form
`∂ᵢαⱼ(x) - ∂ⱼαᵢ(x)` on `F` is the differential of a smooth function, where `αₖ` are the mixed
components of `τ` for the basis `bs`, then there is a two-form `φ` on `EB × F`, smooth on
`U ×ˢ univ`, whose exterior derivative vanishes at every point of `U ×ˢ univ`, and which agrees
with `τ` on every pair of vectors whose second member is tangent to the fibre. In particular `φ`
has the fibre components and the mixed components of `τ`. -/
theorem exists_isClosed_local [FiniteDimensional ℝ EB] [Finite ι] [LinearOrder ι]
    [ConnectedSpace F] {U : Set EB} (hU : IsOpen U)
    (hτ : RoughForm.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst τ.val (U ×ˢ univ))
    (h : ∀ i j, ∀ x ∈ U, ∃ g : F → ℝ, ContMDiff IF 𝓘(ℝ) ∞ g ∧ ∀ (y : F) (w : TangentSpace IF y),
      mvfderiv IF g y w = RoughForm.mixedCurl τ.val bs i j x y w) :
    ∃ φ : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2,
      ContMDiffOn (𝓘(ℝ, EB).prod IF)
        ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (φ z)) (U ×ˢ univ) ∧
      (∀ z ∈ U ×ˢ univ, mextDeriv φ z = 0) ∧
      ∀ z (v : TangentSpace (𝓘(ℝ, EB).prod IF) z) (w : TangentSpace IF z.2),
        φ z ![v, ((0 : EB), w)] = τ.val z ![v, ((0 : EB), w)] := by
  classical
  obtain ⟨y₀⟩ := ‹ConnectedSpace F›.toNonempty
  have := Fintype.ofFinite ι
  choose f hfs hf₀ hfd using fun i j ↦
    exists_contMDiffOn_mvfderiv_eq_mixedCurl τ bs hU (h i j) y₀
  let θ (i j : ι) : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F) :=
    SmoothForm.mpullback Prod.fst contMDiff_fst
      (SmoothForm.wedge (bs.coordOneForm i) (bs.coordOneForm j))
  have hθ (i j : ι) (z : EB × F) (v w : TangentSpace (𝓘(ℝ, EB).prod IF) z) :
      (θ i j).val z ![v, w] =
        bs.coord i v.1 * bs.coord j w.1 - bs.coord i w.1 * bs.coord j v.1 :=
    bs.mpullback_fst_wedge_coordOneForm_apply i j z v w
  let g (i j : ι) (z : EB × F) : ℝ := f i j z - RoughForm.baseComponent τ.val bs i j z.1 z.2
  let φ : RoughForm (𝓘(ℝ, EB).prod IF) (EB × F) ℝ 2 :=
    τ.val + ∑ i, ∑ j with i < j, g i j • (θ i j).val
  have hφ (z : EB × F) (v w : TangentSpace (𝓘(ℝ, EB).prod IF) z) :
      φ z ![v, w] = τ.val z ![v, w] +
        ∑ i, ∑ j with i < j, g i j z * (θ i j).val z ![v, w] := by
    simp only [φ, Pi.add_apply, ContinuousAlternatingMap.add_apply, Finset.sum_apply,
      ContinuousAlternatingMap.sum_apply, Pi.smul_apply', ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
  -- `φ` agrees with `τ` as soon as one vector is vertical.
  have hvert (z : EB × F) (v : TangentSpace (𝓘(ℝ, EB).prod IF) z) (w : TangentSpace IF z.2) :
      φ z ![v, ((0 : EB), w)] = τ.val z ![v, ((0 : EB), w)] := by
    refine (hφ _ _ _).trans (add_eq_left.2 (Finset.sum_eq_zero fun i _ ↦
      Finset.sum_eq_zero fun j _ ↦ mul_eq_zero_of_right _ ((hθ i j z v ((0 : EB), w)).trans ?_)))
    simp
  have hvert' (z : EB × F) (v : TangentSpace (𝓘(ℝ, EB).prod IF) z) (w : TangentSpace IF z.2) :
      φ z ![((0 : EB), w), v] = τ.val z ![((0 : EB), w), v] := by
    exact ((φ z).apply_vecCons_swap _ _).trans (((congrArg Neg.neg (hvert z v w))).trans
      ((τ.val z).apply_vecCons_swap _ _).symm)
  -- The base components of `φ` are the primitives `f i j`.
  have hbase (z : EB × F) {i j : ι} (hij : i < j) :
      φ z ![(bs i, 0), (bs j, 0)] = f i j z := by
    refine (hφ z (bs i, 0) (bs j, 0)).trans ?_
    have e (k l : ι) : (θ k l).val z ![((bs i, 0) : TangentSpace (𝓘(ℝ, EB).prod IF) z),
        (bs j, 0)] =
          bs.coord k (bs i) * bs.coord l (bs j) - bs.coord k (bs j) * bs.coord l (bs i) :=
      hθ k l z _ _
    simp only [e]
    rw [bs.sum_sum_mul_coord_mul_sub_coord_mul (fun k l ↦ g k l z) hij]
    simp only [g, RoughForm.baseComponent_def]
    ring
  -- The fibre and mixed components of `φ` are those of `τ`.
  have hfib : RoughForm.fiberComponent φ = RoughForm.fiberComponent τ.val := by
    funext x y
    refine ContinuousAlternatingMap.ext_fin_two fun w₁ w₂ ↦ ?_
    rw [RoughForm.fiberComponent_apply, RoughForm.fiberComponent_apply]
    exact hvert _ _ w₂
  have hmix : RoughForm.mixedComponent φ bs = RoughForm.mixedComponent τ.val bs := by
    funext i x y
    refine ContinuousAlternatingMap.ext fun u ↦ ?_
    rw [show u = ![u 0] from funext fun k ↦ by fin_cases k; rfl,
      RoughForm.mixedComponent_apply, RoughForm.mixedComponent_apply]
    exact hvert' (x, y) _ (u 0)
  have hfdc : RoughForm.fderivFiberComponent φ = RoughForm.fderivFiberComponent τ.val := by
    funext x v
    simp only [RoughForm.fderivFiberComponent_def, hfib]
  -- `φ` is smooth over the patch.
  have hsm : ContMDiffOn (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) ∞
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (φ z)) (U ×ˢ univ) := by
    have hsum : ContMDiffOn (𝓘(ℝ, EB).prod IF)
        ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z
          (∑ i, ∑ j with i < j, (g i j • (θ i j).val) z)) (U ×ˢ univ) :=
      ContMDiffOn.sum_section fun i _ ↦ ContMDiffOn.sum_section fun j _ ↦
        ContMDiffOn.smul_section ((hfs i j).sub (contMDiff_baseComponent τ bs i j).contMDiffOn)
          (θ i j).contMDiff.contMDiffOn
    exact τ.contMDiff.contMDiffOn.add_section
      (hsum.congr fun z _ ↦ by simp only [Finset.sum_apply])
  have hW : IsOpen (U ×ˢ (univ : Set F)) := hU.prod isOpen_univ
  have hsmAt {z : EB × F} (hz : z ∈ U ×ˢ univ) := hsm.contMDiffAt (hW.mem_nhds hz)
  have hτAt (z : EB × F) : ContMDiffAt (𝓘(ℝ, EB).prod IF)
      ((𝓘(ℝ, EB).prod IF).prod 𝓘(ℝ, (EB × EF) [⋀^Fin 2]→L[ℝ] ℝ)) 1
      (fun z ↦ Bundle.TotalSpace.mk' ((EB × EF) [⋀^Fin 2]→L[ℝ] ℝ) z (τ.val z)) z :=
    (τ.contMDiff z).of_le (by norm_num)
  -- Two fibre vectors: vertical closedness of `τ`.
  have hff {x : EB} {y : F} (hz : (x, y) ∈ U ×ˢ univ) (w₁ w₂ : TangentSpace IF y)
      (v : TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) :
      mextDeriv φ (x, y) ![((0 : EB), w₁), (0, w₂), v] = 0 := by
    refine (RoughForm.mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum _ bs
      ((hsmAt hz).of_le (by norm_num)) w₁ w₂ v).trans ?_
    simp only [hfdc, hfib, hmix]
    refine (RoughForm.mextDeriv_apply_eq_mextDeriv_fiberComponent_add_sum _ bs
      (hτAt _) w₁ w₂ v).symm.trans ?_
    exact RoughForm.isVerticallyClosedOn_iff.1 hτ (x, y) hz _ (mem_ker_mfderiv_fst_iff.2 rfl) _
      (mem_ker_mfderiv_fst_iff.2 rfl) v
  -- Two base vectors and a fibre vector: the choice of the primitives `f i j`.
  have hsnoc (z : EB × F) (u : Fin 1 → TangentSpace (𝓘(ℝ, EB).prod IF) z)
      (w : TangentSpace IF z.2) :
      φ z (Fin.snoc u (((0 : EB), w) : EB × EF)) =
        τ.val z (Fin.snoc u (((0 : EB), w) : EB × EF)) := by
    rw [show (Fin.snoc u ((0 : EB), w) : Fin 2 → TangentSpace (𝓘(ℝ, EB).prod IF) z) =
      ![u 0, ((0 : EB), w)] from funext fun k ↦ by fin_cases k <;> rfl]
    exact hvert z (u 0) w
  have hbbf₀ {x : EB} {y : F} (hz : (x, y) ∈ U ×ˢ univ) (w : TangentSpace IF y) {i j : ι}
      (hij : i < j) :
      mextDeriv φ (x, y) ![(bs i, 0), (bs j, 0), ((0 : EB), w)] = 0 := by
    have e : (![(bs i, 0), (bs j, 0), ((0 : EB), w)] :
        Fin 3 → TangentSpace (𝓘(ℝ, EB).prod IF) (x, y)) =
        Fin.snoc (fun k ↦ (![bs i, bs j] k, 0)) ((0 : EB), w) :=
      funext fun k ↦ by fin_cases k <;> rfl
    have hφb : (fun y' ↦ φ (x, y') fun k ↦ (![bs i, bs j] k, (0 : EF))) =
        fun y' ↦ f i j (x, y') := by
      funext y'
      rw [← hbase (x, y') hij]
      exact congrArg _ (funext fun k ↦ by fin_cases k <;> rfl)
    have hτb : (fun y' ↦ τ.val (x, y') fun k ↦ (![bs i, bs j] k, (0 : EF))) =
        RoughForm.baseComponent τ.val bs i j x := by
      funext y'
      rw [RoughForm.baseComponent_def]
      exact congrArg _ (funext fun k ↦ by fin_cases k <;> rfl)
    have h₁ := RoughForm.mextDeriv_prod_apply_snoc_inr
      ((hsmAt hz).mdifferentiableAt (by simp)) ![bs i, bs j] w
    have h₂ := RoughForm.mextDeriv_prod_apply_snoc_inr
      ((τ.contMDiff (x, y)).mdifferentiableAt (by simp)) ![bs i, bs j] w
    rw [hφb, hfd i j x hz.1] at h₁
    rw [hτb] at h₂
    have h₃ := mixedCurl_eq_mvfderiv_baseComponent_sub_mextDeriv τ bs i j x y w
    have h₄ := h₃.trans (congrArg (_ - ·) ((congrArg (mextDeriv τ.val (x, y)) e).trans h₂))
    rw [e]
    refine h₁.trans ?_
    rw [h₄]
    have key {R V : Type _} [Ring R] [AddCommGroup V] [Module R V] {A B D : V} (c : R)
        (hc : c = 1) (hAB : A = B) : A + c • (D - (B + c • D)) = 0 := by
      rw [hc, hAB, one_smul, one_smul]
      abel
    refine key _ ?_ ?_
    · norm_num
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      congr 3
      funext q
      exact hsnoc (q, y) _ w
  have hbbf {x : EB} {y : F} (hz : (x, y) ∈ U ×ˢ univ) (a b : EB) (w : TangentSpace IF y) :
      mextDeriv φ (x, y) ![(a, 0), (b, 0), ((0 : EB), w)] = 0 :=
    (mextDeriv φ (x, y)).apply_vecCons_inl_inl_inr_eq_zero_of_basis bs w
      (fun i j hij ↦ hbbf₀ hz w hij) a b
  -- Three base vectors: `dφ` there is constant along the fibres and vanishes at `y₀`.
  have hbbb {x : EB} {y : F} (hz : (x, y) ∈ U ×ˢ univ) (a b c : EB) :
      mextDeriv φ (x, y) ![(a, 0), (b, 0), (c, 0)] = 0 := by
    have h := RoughForm.mextDeriv_prod_apply_inl_eq_zero (n := 2) (φ := φ) hU
      (hsm.of_le (by norm_num)) (fun p hp y' a' v ↦ ?_) (x₀ := y₀) (fun p hp a' ↦ ?_) hz.1 y
      ![a, b, c]
    · refine Eq.trans (congrArg _ (funext fun k ↦ ?_)) h
      fin_cases k <;> rfl
    · refine Eq.trans (congrArg _ (funext fun k ↦ ?_)) (hbbf ⟨hp, mem_univ y'⟩ (a' 0) (a' 1) v)
      fin_cases k <;> rfl
    · refine Eq.trans (congrArg _ (funext fun k ↦ ?_))
        ((φ (p, y₀)).apply_vecCons_inl_eq_zero_of_basis bs (fun i j hij ↦ ?_) (a' 0) (a' 1))
      · fin_cases k <;> rfl
      · refine (hbase (p, y₀) hij).trans ?_
        exact hf₀ i j p hp
  refine ⟨φ, hsm, fun z hz ↦ ?_, hvert⟩
  obtain ⟨x, y⟩ := z
  exact ContinuousAlternatingMap.eq_zero_of_forall_prod_fin_three (mextDeriv φ (x, y))
    (fun w₁ w₂ v ↦ hff hz w₁ w₂ v) (fun a b w ↦ hbbf hz a b w) (fun a b c ↦ hbbb hz a b c)

end TauCeti.SmoothTwoForm

end
