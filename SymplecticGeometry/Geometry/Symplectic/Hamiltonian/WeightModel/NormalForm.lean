/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.NormalForm
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Geometry.Manifold.GroupAction.BoundarylessModel
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
import SymplecticGeometry.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The weight chart of a Hamiltonian torus action, with period-one weights

Let a compact commutative Lie group `G`, such as a torus, act smoothly on a finite-dimensional
symplectic manifold `(M, σ)` without boundary, preserving `σ`, with a moment map `μ` in the
library's sign, `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` (so that Tau Ceti's moment map is `-μ`), and let `p` be a
fixed point. This file reads Tau Ceti's weight chart
`TauCeti.SmoothTwoForm.IsMomentMap.exists_weightModelChart` in the library's conventions
(`SymplecticGeometry.exists_weightChart`; with the fundamental vector fields,
`SymplecticGeometry.exists_weightChart_fundamentalVectorField`, which gives a chart with all the
properties below, bundled as `SymplecticGeometry.IsWeightChart`):

* the chart goes from the model to `M`: it is the inverse of Tau Ceti's chart, composed with
  `EuclideanSpace.sumEquivProd`, and is defined on a round ball of `StdSpace (Fin n)`, centred at
  `0`, which it sends to `p`;
* it pulls `σ` back to `stdForm (Fin n)`, by `isSymplectomorphism_sumEquivProd`;
* the weights have period one: `αₖ = α^{TC}ₖ / 2π`, so that `χₖ (exp ξ) = e^{2π i αₖ(ξ)}`, and
  they lie in the character lattice, `αₖ(ξ) ∈ ℤ` whenever `exp ξ = 1`;
* `g` acts in the complex coordinates `z = complexToRealEuclidean (Fin n) u` by `uₖ ↦ χₖ(g) uₖ`;
* the differential of `Φ` sends the generator `(x, y) ↦ (-2π αₖ(ξ) yₖ, 2π αₖ(ξ) xₖ)` of the
  weight rotation to the fundamental vector field `ξ_M`;
* `μ(Φ z) = μ(p) + π Σₖ |zₖ|² αₖ`, where `|zₖ|² = xₖ(z)² + yₖ(z)²`.

Zero weights are allowed, and neither compactness of `M` nor isolatedness of `p` is assumed.

Only `M` is assumed boundaryless (`BoundarylessManifold`), not its model. Tau Ceti's chart needs a
model without boundary, so it is taken on the copy `TauCeti.BoundarylessModel I' M` of `M`,
modelled on `E'`, with the carried action, the pulled back form and the composed moment map
(moment maps pull back by `TauCeti.SmoothTwoForm.IsMomentMap.mpullback`), and carried back to `M`
along `TauCeti.BoundarylessModel.interiorDiffeomorph`: weight charts move along equivariant
diffeomorphisms (`SymplecticGeometry.IsWeightChart.trans_diffeomorph`).

## References

* [A. Cannas da Silva, *Symplectic Toric Manifolds*][CannasdaSilva2001], Theorems 3.1.1–3.1.2
* [V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*][GuilleminSternberg1990],
  Theorems 22.1 and 32.1
-/

public section

noncomputable section

open Real
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section IsWeightChart

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {σ : SmoothTwoForm I' M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [MulAction G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **A weight chart at a fixed point.** `Φ` is a weight chart of the action of `G` on `(M, σ)`
with moment map `μ`, at `p`, with characters `χₖ : G → S¹`, period-one weights `αₖ ∈ 𝔤*` and
radius `r`, if

* `χₖ (exp ξ) = e^{2π i αₖ(ξ)}`;
* the source of `Φ` is the ball of radius `r > 0` about `0` in `StdSpace (Fin n)`, and
  `Φ 0 = p`;
* in the complex coordinates `z = complexToRealEuclidean (Fin n) u`, `Φ` is equivariant for the
  action `uₖ ↦ χₖ(g) uₖ` of `g` on the ball;
* `Φ` pulls `σ` back to the standard form `stdForm (Fin n)` on the ball;
* at every `z` in the ball and for every `ξ ∈ 𝔤`, the differential of `Φ` at `z` sends the
  generator `(-2π αₖ(ξ) yₖ(z), 2π αₖ(ξ) xₖ(z))` of the weight rotation, read through
  `EuclideanSpace.sumEquivProd`, to the fundamental vector field `ξ_M` at `Φ z`;
* `μ (Φ z) = μ p + π Σₖ (xₖ(z)² + yₖ(z)²) αₖ` on the ball.

The weights then lie in the character lattice
(`SymplecticGeometry.IsWeightChart.exists_int_of_mulInvariantExp_eq_one`), and the target of `Φ`
is `G`-invariant (`SymplecticGeometry.IsWeightChart.smul_mem_target`). -/
structure IsWeightChart (σ : SmoothTwoForm I' M) (μ : M → Module.Dual ℝ (GroupLieAlgebra I G))
    (p : M) {n : ℕ} (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
    (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞) (r : ℝ) :
    Prop where
  /-- The characters are the exponentials of the period-one weights. -/
  apply_mulInvariantExp : ∀ k (ξ : GroupLieAlgebra I G),
    χ k (mulInvariantExp (I := I) ξ) = Circle.exp (2 * π * α k ξ)
  /-- The radius is positive. -/
  radius_pos : 0 < r
  /-- The source is the ball of radius `r` about `0`. -/
  source_eq : Φ.source = Metric.ball 0 r
  /-- The chart is centred at `p`. -/
  apply_zero : Φ 0 = p
  /-- `Φ` is equivariant, for the action of `g` by `uₖ ↦ χₖ(g) uₖ` in complex coordinates. -/
  equivariant : ∀ g : G, ∀ u : Fin n → ℂ, complexToRealEuclidean (Fin n) u ∈ Φ.source →
    complexToRealEuclidean (Fin n) (fun k ↦ (χ k g : ℂ) * u k) ∈ Φ.source ∧
      Φ (complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
        g • Φ (complexToRealEuclidean (Fin n) u)
  /-- `Φ` pulls `σ` back to the standard form on its source. -/
  isSymplecticMapOn : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ Φ Φ.source
  /-- The differential of `Φ` sends the generator of the weight rotation to `ξ_M`. -/
  mfderiv_weightGenerator : ∀ z ∈ Φ.source, ∀ ξ : GroupLieAlgebra I G,
    mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z
        (EuclideanSpace.sumEquivProd.symm
          (weightGenerator (fun k ↦ 2 * π * α k ξ) (EuclideanSpace.sumEquivProd z))) =
      fundamentalVectorField I' ξ (Φ z)
  /-- The moment map is quadratic in the chart. -/
  momentMap_apply : ∀ z ∈ Φ.source, ∀ ξ : GroupLieAlgebra I G,
    μ (Φ z) ξ = μ p ξ + π * ∑ k, α k ξ * (z.x k ^ 2 + z.y k ^ 2)

namespace IsWeightChart

variable {p : M} {n : ℕ} {χ : Fin n → G →ₜ* Circle} {α : Fin n → StrongDual ℝ E}
  {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞} {r : ℝ}

/-- The centre `0` of a weight chart lies in its source. -/
theorem zero_mem_source (h : IsWeightChart σ μ p χ α Φ r) : 0 ∈ Φ.source := by
  rw [h.source_eq]
  exact Metric.mem_ball_self h.radius_pos

/-- The fixed point `p` lies in the target of a weight chart at `p`. -/
theorem mem_target (h : IsWeightChart σ μ p χ α Φ r) : p ∈ Φ.target := by
  rw [← h.apply_zero]
  exact Φ.map_source h.zero_mem_source

/-- The weights of a weight chart lie in the character lattice: `αₖ(ξ) ∈ ℤ` whenever
`exp ξ = 1`. -/
theorem exists_int_of_mulInvariantExp_eq_one (h : IsWeightChart σ μ p χ α Φ r) (k : Fin n)
    {ξ : GroupLieAlgebra I G} (hξ : mulInvariantExp (I := I) ξ = 1) : ∃ m : ℤ, α k ξ = m := by
  have h1 : Circle.exp (2 * π * α k ξ) = 1 := by
    rw [← h.apply_mulInvariantExp, hξ, map_one]
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.1 h1
  refine ⟨m, ?_⟩
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hπ
  rw [hm, mul_comm]

/-- The target of a weight chart is invariant under the action of `G`. -/
theorem smul_mem_target (h : IsWeightChart σ μ p χ α Φ r) (g : G) {x : M} (hx : x ∈ Φ.target) :
    g • x ∈ Φ.target := by
  obtain ⟨u, hu⟩ := (complexToRealEuclidean (Fin n)).surjective (Φ.symm x)
  have hsrc : complexToRealEuclidean (Fin n) u ∈ Φ.source := hu ▸ Φ.map_target hx
  obtain ⟨h₁, h₂⟩ := h.equivariant g u hsrc
  have hx' : Φ (complexToRealEuclidean (Fin n) u) = x := by rw [hu]; exact Φ.right_inv hx
  rw [← hx', ← h₂]
  exact Φ.map_source h₁

/-- The centre `p` of a weight chart is fixed by every `g : G`. -/
theorem smul_eq (h : IsWeightChart σ μ p χ α Φ r) (g : G) : g • p = p := by
  have h₀ : complexToRealEuclidean (Fin n) 0 ∈ Φ.source := by
    rw [map_zero]; exact h.zero_mem_source
  have h0 := (h.equivariant g 0 h₀).2
  simp only [Pi.zero_apply, mul_zero] at h0
  rw [← Pi.zero_def, map_zero, h.apply_zero] at h0
  exact h0.symm

/-- On the target of a weight chart, `Φ⁻¹` intertwines the action of `g` with the rotation
`uₖ ↦ χₖ(g) uₖ` in the complex coordinates `z = complexToRealEuclidean (Fin n) u`. -/
theorem symm_smul (h : IsWeightChart σ μ p χ α Φ r) (g : G) {y : M} (hy : y ∈ Φ.target) :
    Φ.symm (g • y) = complexToRealEuclidean (Fin n) fun k ↦
      (χ k g : ℂ) * (complexToRealEuclidean (Fin n)).symm (Φ.symm y) k := by
  set C := complexToRealEuclidean (Fin n)
  have hu : C (C.symm (Φ.symm y)) ∈ Φ.source := by
    rw [C.apply_symm_apply]; exact Φ.map_target hy
  obtain ⟨h₁, h₂⟩ := h.equivariant g _ hu
  rw [PartialDiffeomorph.symm_toPartialEquiv] at h₁ h₂ ⊢
  rw [C.apply_symm_apply, Φ.right_inv hy] at h₂
  rw [← h₂, Φ.left_inv h₁]

/-- The model space of a manifold that has a weight chart from `StdSpace (Fin n)` has real
dimension `2 * n`. -/
theorem finrank_eq (h : IsWeightChart σ μ p χ α Φ r) : Module.finrank ℝ E' = 2 * n := by
  rw [← ((Φ.isLocalDiffeomorphAt _ _ ∞ h.zero_mem_source).finrank_eq (by simp)),
    finrank_stdSpace, Fintype.card_fin]

/-- On a manifold modelled on a space of real dimension `2 * m`, a weight chart is defined on
`StdSpace (Fin m)`: `n = m`. -/
theorem eq_of_finrank_eq (h : IsWeightChart σ μ p χ α Φ r) {m : ℕ}
    (hE : Module.finrank ℝ E' = 2 * m) : n = m := by
  have := h.finrank_eq
  omega

/-- **Weight charts are carried along equivariant diffeomorphisms.** If `ψ : N → M` is a
`G`-equivariant diffeomorphism and `Φ` is a weight chart at `q` of the action on `N`, for the
pulled back form `ψ^* σ` and the moment map `μ ∘ ψ`, then `ψ ∘ Φ` is a weight chart at `ψ q` of
the action on `(M, σ)` with moment map `μ`, with the same characters, weights and radius. -/
theorem trans_diffeomorph {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] [IsManifold I'' ∞ N] [MulAction G N]
    [ContMDiffSMul I I'' ∞ G N] {q : N}
    {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I'' (StdSpace (Fin n)) N ∞}
    (ψ : N ≃ₘ⟮I'', I'⟯ M) (hψ : ∀ (g : G) (y : N), ψ (g • y) = g • ψ y)
    (h : IsWeightChart (SmoothForm.mpullback ψ ψ.contMDiff σ) (μ ∘ ψ) q χ α Φ r) :
    IsWeightChart σ μ (ψ q) χ α (Φ.trans ψ.toPartialDiffeomorph) r := by
  have hcoe : ⇑(Φ.trans ψ.toPartialDiffeomorph) = ψ ∘ Φ := by
    rw [PartialDiffeomorph.coe_trans]
    simp [Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  have hsrc : (Φ.trans ψ.toPartialDiffeomorph).source = Φ.source := by
    rw [PartialDiffeomorph.trans_source]
    simp
  refine ⟨h.apply_mulInvariantExp, h.radius_pos, hsrc.trans h.source_eq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoe, Function.comp_apply, h.apply_zero]
  · intro g u hu
    rw [hsrc] at hu ⊢
    obtain ⟨h₁, h₂⟩ := h.equivariant g u hu
    refine ⟨h₁, ?_⟩
    rw [hcoe, Function.comp_apply, Function.comp_apply, h₂, hψ]
  · rw [hcoe, hsrc]
    exact ((SmoothTwoForm.isSymplecticMap_mpullback σ ψ.contMDiff).isSymplecticMapOn _).comp
      h.isSymplecticMapOn (Set.mapsTo_univ _ _) (fun _ _ ↦ ψ.mdifferentiable (by simp) _)
      (fun z hz ↦ Φ.mdifferentiableAt (by simp) hz)
  · intro z hz (ξ : E)
    rw [hsrc] at hz
    have hd := mfderiv_comp_apply (x := z) (f := Φ) (g := ψ) (ψ.mdifferentiable (by simp) (Φ z))
      (Φ.mdifferentiableAt (by simp) hz) (EuclideanSpace.sumEquivProd.symm
        (weightGenerator (fun k ↦ 2 * π * α k ξ) (EuclideanSpace.sumEquivProd z)))
    rw [h.mfderiv_weightGenerator z hz ξ] at hd
    rw [hcoe]
    refine hd.trans ?_
    -- The orbit map `g ↦ g • Φ z` of `N` is differentiable.
    have horbit : MDifferentiableAt I I'' (fun g : G ↦ g • Φ z) 1 :=
      ((contMDiff_smul (I := I) (I' := I'') (n := ∞)).comp
        (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)
    exact mfderiv_fundamentalVectorField_of_map_smul (ψ.mdifferentiable (by simp) _) horbit
      (fun g ↦ hψ g _) ξ
  · intro z hz ξ
    rw [hcoe, Function.comp_apply]
    exact h.momentMap_apply z (hsrc ▸ hz) ξ

end IsWeightChart

end IsWeightChart

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {σ : SmoothTwoForm I' M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [CommGroup G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- The weight chart of `SymplecticGeometry.exists_weightChart_fundamentalVectorField`, when the
model of `M` has no boundary: Tau Ceti's chart, read in the library's conventions. -/
private theorem exists_weightChart_fundamentalVectorField_of_boundaryless [I'.Boundaryless]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞) (r : ℝ),
      IsWeightChart σ μ p χ α Φ r := by
  obtain ⟨n, χ, β, chart, r, hβ, -, hpchart, hchartp, hr, htarget, hequiv, hform, hvf, hmom⟩ :=
    hμ.exists_weightModelChart hσ hG hp
  let A : StdSpace (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.sumEquivProd
  -- Compose Tau Ceti's chart with `A⁻¹`, a symplectomorphism onto the standard model.
  obtain ⟨-, -, hderiv, hform'⟩ := SmoothTwoForm.trans_toDiffeomorph_darbouxChart hform A.symm
    isSymplectomorphism_sumEquivProd.symm
  let chart' := chart.trans A.symm.toDiffeomorph.toPartialDiffeomorph
  let Φ := chart'.symm
  have hΦ : ∀ z, Φ z = chart.symm (A z) := fun z ↦ by simp [Φ, chart']
  have hsrc : Φ.source = A ⁻¹' chart.target := by
    ext z; simp [Φ, chart']
  have htgt : Φ.target = chart.source := by
    simp [Φ, chart']
  -- On the source, `chart ∘ Φ` is `A`.
  have hmem {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : A z ∈ chart.target := by
    rwa [hsrc] at hz
  have hchartΦ {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : chart (Φ z) = A z := by
    rw [hΦ]; exact chart.right_inv (hmem hz)
  have hΦsrc {z : StdSpace (Fin n)} (hz : z ∈ Φ.source) : Φ z ∈ chart.source := by
    rw [← htgt]; exact Φ.map_source hz
  let α : Fin n → StrongDual ℝ E := fun k ↦ (2 * π)⁻¹ • β k
  have hα (k : Fin n) (ξ : E) : α k ξ = (2 * π)⁻¹ * β k ξ := by
    simp only [α, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hβα (k : Fin n) (ξ : E) : β k ξ = 2 * π * α k ξ := by
    rw [hα, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_mul]
  refine ⟨n, χ, α, Φ, r, fun k ξ ↦ by rw [hβ, hβα k ξ], hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    rw [hsrc, Set.mem_preimage, htarget, Set.mem_ofPred_eq, EuclideanSpace.norm_sq_sumEquivProd,
      mem_ball_zero_iff, sq_lt_sq₀ (norm_nonneg _) hr.le]
  · rw [hΦ, map_zero, ← hchartp]; exact chart.left_inv hpchart
  · intro g u hu
    obtain ⟨h₁, h₂⟩ := hequiv g _ (hΦsrc hu)
    have hrot : A (complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
        chart (g • Φ (complexToRealEuclidean (Fin n) u)) := by
      rw [h₂, hchartΦ hu, weightRotation_sumEquivProd_complexToRealEuclidean]
      simp only [A, ← Circle.coe_exp, Circle.exp_arg]
    refine ⟨?_, ?_⟩
    · rw [hsrc, Set.mem_preimage, hrot]; exact chart.map_source h₁
    · rw [hΦ, hrot]; exact chart.left_inv h₁
  · refine SmoothTwoForm.isSymplecticMapOn_iff.2 fun z hz v w ↦ ?_
    -- `chart'` undoes the differential of its inverse `Φ`.
    have hd (u : StdSpace (Fin n)) :
        mvfderiv I' chart' (Φ z) (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z u) = u := by
      rw [mvfderiv_apply_eq_mfderiv_apply]
      exact chart'.mfderiv_apply_mfderiv_symm_apply (by simp) hz u
    rw [SymplecticForm.constSmooth_apply (stdForm (Fin n)) z v w, hform' _ (hΦsrc hz), hd v, hd w]
  · intro z hz (ξ : E)
    -- Tau Ceti's chart sends `ξ_M` to the generator; `chart'` is that chart followed by
    -- `A⁻¹`, and `Φ` is the inverse of `chart'`. As in the moment map step below, `ξ` is
    -- read in the model space `E`.
    have h := chart'.mfderiv_symm_apply_mfderiv_apply (by simp)
      (by simpa [chart'] using hΦsrc hz) (fundamentalVectorField (I := I) (G := G) I' ξ (Φ z))
    rw [← mvfderiv_apply_eq_mfderiv_apply (f := chart'), hderiv (Φ z),
      ContinuousLinearMap.comp_apply, mvfderiv_apply_eq_mfderiv_apply, hvf _ (hΦsrc hz) ξ,
      weightInfinitesimalAction_apply, hchartΦ hz,
      show chart' (Φ z) = z from chart'.right_inv hz] at h
    simp only [hβα] at h
    exact h
  · -- Tau Ceti's weights are functionals on the model space `E` of `𝔤`; read `ξ` there, as
    -- tactics do not see through `GroupLieAlgebra I G`.
    intro z hz (ξ : E)
    have h := hmom (Φ z) (hΦsrc hz) ξ
    rw [hchartΦ hz] at h
    simp only [weightMomentMap_apply] at h
    simp only [A, StdSpace.sumEquivProd_apply_fst, StdSpace.sumEquivProd_apply_snd, hβα] at h
    have hs : ∑ i, 2 * π * α i ξ * (z.x i ^ 2 + z.y i ^ 2) =
        2 * (π * ∑ i, α i ξ * (z.x i ^ 2 + z.y i ^ 2)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hs] at h
    rw [LinearMap.neg_apply (μ (Φ z)) ξ, LinearMap.neg_apply (μ p) ξ] at h
    linarith

/-- **The weight chart at a fixed point, with the fundamental vector fields.** Under the
hypotheses of `SymplecticGeometry.exists_weightChart`, there is a weight chart at the fixed point
`p` (`SymplecticGeometry.IsWeightChart`): the chart of `SymplecticGeometry.exists_weightChart`,
with all of its properties, whose differential in addition sends the generator of the weight
rotation by the angles `2π αₖ(ξ)` to the fundamental vector field `ξ_M`. -/
theorem exists_weightChart_fundamentalVectorField [BoundarylessManifold I' M]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞) (r : ℝ),
      IsWeightChart σ μ p χ α Φ r := by
  -- Work on the copy `N` of `M` modelled on `E'`, which has no boundary, with the carried
  -- action, the pulled back form and the composed moment map.
  let _ := BoundarylessModel.interiorChartedSpace I' (M := M)
  let N := BoundarylessModel I' M
  let ψ : N ≃ₘ⟮𝓘(ℝ, E'), I'⟯ M := (BoundarylessModel.interiorDiffeomorph I' (M := M) ∞).symm
  have hψ (g : G) (y : N) : ψ (g • y) = g • ψ y :=
    BoundarylessModel.interiorDiffeomorph_symm_smul I' ∞ g y
  have hfund (ξ : GroupLieAlgebra I G) (y : N) :
      mfderiv 𝓘(ℝ, E') I' ψ y (fundamentalVectorField 𝓘(ℝ, E') ξ y) =
        fundamentalVectorField I' ξ (ψ y) :=
    mfderiv_fundamentalVectorField_of_map_smul (ψ.mdifferentiable (by simp) y)
      (((contMDiff_smul (I := I) (I' := 𝓘(ℝ, E')) (n := ∞)).comp
        (contMDiff_id.prodMk contMDiff_const)).mdifferentiableAt (by simp)) (fun g ↦ hψ g y) ξ
  have hμ' := hμ.mpullback (a' := InfinitesimalAction.fundamental I G 𝓘(ℝ, E') N) ψ.contMDiff
    fun ξ y ↦ by simpa only [InfinitesimalAction.fundamental_apply] using hfund ξ y
  have hσ' : SmoothTwoForm.IsSymplectic (SmoothForm.mpullback ψ ψ.contMDiff σ) :=
    (ψ.isLocalDiffeomorph.isSymplectic_mpullback_iff ψ.surjective).2 hσ
  have hG' (g : G) : SmoothForm.mpullback (fun y : N ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) (SmoothForm.mpullback ψ ψ.contMDiff σ) =
        SmoothForm.mpullback ψ ψ.contMDiff σ := by
    have hg := ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') (n := ∞) (M := M) g
    have hcongr : ∀ (f₁ f₂ : N → M) (h₁ : ContMDiff 𝓘(ℝ, E') I' ∞ f₁)
        (h₂ : ContMDiff 𝓘(ℝ, E') I' ∞ f₂), f₁ = f₂ →
        SmoothForm.mpullback (F := ℝ) (k := 2) f₁ h₁ = SmoothForm.mpullback f₂ h₂ := by
      rintro f _ _ _ rfl
      rfl
    rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp,
      hcongr (ψ ∘ fun y : N ↦ g • y) ((fun x : M ↦ g • x) ∘ ψ) _ (hg.comp ψ.contMDiff)
        (funext fun y ↦ hψ g y),
      SmoothForm.mpullback_comp ψ (fun x : M ↦ g • x) ψ.contMDiff hg, LinearMap.comp_apply, hG g]
  have hp' (g : G) : g • ψ.symm p = ψ.symm p := by
    rw [← ψ.symm_apply_apply (g • ψ.symm p), hψ, Diffeomorph.apply_symm_apply, hp]
  obtain ⟨n, χ, α, Φ, r, h⟩ :=
    exists_weightChart_fundamentalVectorField_of_boundaryless (μ := μ ∘ ψ) hμ' hσ' hG' hp'
  refine ⟨n, χ, α, Φ.trans ψ.toPartialDiffeomorph, r, ?_⟩
  simpa only [Diffeomorph.apply_symm_apply] using h.trans_diffeomorph ψ hψ

/-- **The weight chart at a fixed point, with period-one weights.** Let a compact commutative Lie
group `G`, with Lie algebra `𝔤 = E`, act smoothly on a finite-dimensional symplectic manifold
`(M, σ)` without boundary, preserving `σ`, with moment map `μ` in the sign
`d⟨μ, ξ⟩ = -ι_{ξ_M} σ`, that is, `-μ` is a moment map for Tau Ceti's `IsMomentMap`; and let `p`
be a fixed point. Then there are continuous characters `χₖ : G → S¹`, `k < n`, with weights
`αₖ ∈ 𝔤*` of period one, `χₖ (exp ξ) = e^{2π i αₖ(ξ)}`, lying in the character lattice
(`αₖ(ξ) ∈ ℤ` whenever `exp ξ = 1`), and a smooth partial diffeomorphism `Φ` from the ball of
radius `r > 0` about `0` in `StdSpace (Fin n)` onto a `G`-invariant open set of `M`, with
`Φ 0 = p`, such that

* in the complex coordinates `z = complexToRealEuclidean (Fin n) u`, `Φ` is equivariant for the
  action `uₖ ↦ χₖ(g) uₖ` of `g` on the ball;
* `Φ` pulls `σ` back to the standard form `stdForm (Fin n)` on the ball;
* `μ (Φ z) = μ p + π Σₖ (xₖ(z)² + yₖ(z)²) αₖ` on the ball.

Milestone: *Equivariant Darboux theorem and quadratic local moment maps*. -/
theorem exists_weightChart [BoundarylessManifold I' M]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) fun x ↦ -μ x)
    (hσ : σ.IsSymplectic)
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    {p : M} (hp : ∀ g : G, g • p = p) :
    ∃ (n : ℕ) (χ : Fin n → G →ₜ* Circle) (α : Fin n → StrongDual ℝ E)
      (Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I' (StdSpace (Fin n)) M ∞) (r : ℝ),
      (∀ k (ξ : GroupLieAlgebra I G),
        χ k (mulInvariantExp (I := I) ξ) = Circle.exp (2 * π * α k ξ)) ∧
      (∀ k (ξ : GroupLieAlgebra I G), mulInvariantExp (I := I) ξ = 1 → ∃ m : ℤ, α k ξ = m) ∧
      0 < r ∧ Φ.source = Metric.ball 0 r ∧ Φ 0 = p ∧
      (∀ g : G, ∀ x ∈ Φ.target, g • x ∈ Φ.target) ∧
      (∀ g : G, ∀ u : Fin n → ℂ, complexToRealEuclidean (Fin n) u ∈ Φ.source →
        complexToRealEuclidean (Fin n) (fun k ↦ (χ k g : ℂ) * u k) ∈ Φ.source ∧
        Φ (complexToRealEuclidean (Fin n) fun k ↦ (χ k g : ℂ) * u k) =
          g • Φ (complexToRealEuclidean (Fin n) u)) ∧
      (∀ z ∈ Φ.source, ∀ v w : StdSpace (Fin n),
        σ.eval₂ (Φ z) (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z v)
          (mfderiv 𝓘(ℝ, StdSpace (Fin n)) I' Φ z w) = stdForm (Fin n) v w) ∧
      ∀ z ∈ Φ.source, ∀ ξ : GroupLieAlgebra I G,
        μ (Φ z) ξ = μ p ξ + π * ∑ k, α k ξ * (z.x k ^ 2 + z.y k ^ 2) := by
  obtain ⟨n, χ, α, Φ, r, h⟩ := exists_weightChart_fundamentalVectorField hμ hσ hG hp
  exact ⟨n, χ, α, Φ, r, h.apply_mulInvariantExp,
    fun k _ hξ ↦ h.exists_int_of_mulInvariantExp_eq_one k hξ, h.radius_pos, h.source_eq,
    h.apply_zero, fun g _ hx ↦ h.smul_mem_target g hx, h.equivariant,
    fun z hz v w ↦ (h.isSymplecticMapOn.apply hz v w).trans
      (SymplecticForm.constSmooth_apply (stdForm (Fin n)) z v w),
    h.momentMap_apply⟩

end SymplecticGeometry

end
