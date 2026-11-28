/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.KempfNess.Basic

/-!
# The stabilizer in the complexification of a zero of the moment map

Let the action of the complexification `Gc` of `G` on `M` be a complexified action, with `-μ` an
equivariant moment map for `σ` and the metric `g(u, w) = σ(u, J w)`. At a zero `x` of `μ`, the
stabilizer of `x` in `Gc` is read off from the polar decomposition `g = expI η * toHom u`: `g`
fixes `x` exactly when `u` fixes `x` and the fundamental vector field of `η` vanishes at `x`. In
other words, the polar decomposition maps the product of the isotropy algebra and the stabilizer
of `x` in `G` onto the stabilizer of `x` in `Gc`.

## Main results

* `SymplecticGeometry.IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero`: if `μ x = 0`,
  then `g` fixes `x` exactly when, for `(η, u) = C.polar.symm g`, the fundamental vector field of
  `η` vanishes at `x` and `u` fixes `x`.

## Implementation notes

The proof follows [GeorgoulasRobbinSalamon2021], Lemma 2.3. If `g` fixes `x`, then
`y = toHom u • x` is again a zero of `μ` (`IsComplexifiedAction.moment_toHom_smul`), and
`expI η • y = x`; so `⟨μ, η⟩` takes the same value `0` at `y` and at `expI η • y`, and
`expI_smul_eq_self_of_moment_apply_le` gives `expI η • y = y`, that is `y = x`. Then `expI η`
fixes `x`, so does `expI (-η)`, and `moment_expI_neg_smul_apply_pos` rules out a nonzero
fundamental vector field of `η` at `x`. Conversely `expI η` fixes the zeros of the fundamental
vector field of `η` (`IsComplexifiedAction.expI_smul_smul_eq_self_iff`).

## References

* [V. Georgoulas, J. W. Robbin and D. A. Salamon, *The Moment-Weight Inequality and the
  Hilbert–Mumford Criterion*][GeorgoulasRobbinSalamon2021], Lemma 2.3.
-/

public section

open _root_.Bundle Manifold TauCeti
open scoped Manifold ContDiff RealInnerProductSpace

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EC : Type*} [NormedAddCommGroup EC] [NormedSpace ℝ EC] [CompleteSpace EC]
  {HC : Type*} [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  {Gc : Type*} [TopologicalSpace Gc] [ChartedSpace HC Gc] [Group Gc] [LieGroup IC ∞ Gc]
  [T2Space Gc] [BoundarylessManifold IC Gc]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  [MulAction G M] [MulAction Gc M] [ContMDiffSMul I I' ∞ G M] [ContMDiffSMul IC I' ∞ Gc M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I' x)]
  {σ : SmoothTwoForm I' M} {J : SmoothAlmostComplexStructure I' M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {C : LieComplexification I G IC Gc}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **The stabilizer in `Gc` of a zero of the moment map.** For a complexified action on a
Hausdorff manifold without boundary, with `-μ` an equivariant moment map for `σ` and the metric
`g(u, w) = σ(u, J w)`, let `μ x = 0`. Then `g : Gc` fixes `x` exactly when, writing
`(η, u) = C.polar.symm g`, so that `g = C.expI η * C.toHom u`, the fundamental vector field of `η`
for the action of `G` vanishes at `x` and `u` fixes `x`. -/
theorem IsComplexifiedAction.mem_stabilizer_iff_of_moment_eq_zero [T2Space M]
    [BoundarylessManifold I' M] (h : IsComplexifiedAction C J)
    (hμ : σ.IsEquivariantMomentMap fun x ↦ -μ x)
    (hg : ∀ x (u w : TangentSpace I' x), ⟪u, w⟫ = σ.eval₂ x u (J x w)) {x : M} (hx : μ x = 0)
    (g : Gc) :
    g ∈ MulAction.stabilizer Gc x ↔
      fundamentalVectorField (I := I) (G := G) I' (C.polar.symm g).1 x = 0 ∧
        (C.polar.symm g).2 ∈ MulAction.stabilizer G x := by
  conv_lhs => rw [← C.expI_mul_toHom_polar_symm g]
  generalize C.polar.symm g = p
  -- The polar coordinates live in `E × G`; read the first as an element of the Lie algebra, as
  -- the lemmas on `C.expI` take it.
  obtain ⟨η, u⟩ : GroupLieAlgebra I G × G := p
  simp only [MulAction.mem_stabilizer_iff, mul_smul, h.toHom_smul]
  refine ⟨fun hfix ↦ ?_, fun ⟨hX, hu⟩ ↦ ?_⟩
  · -- `u • x` is a zero of `μ` that `expI η` carries to the zero `x`.
    have hy : μ (u • x) = 0 := by
      rw [← h.toHom_smul, h.moment_toHom_smul hμ, hx, map_zero]
    have hux : u • x = x :=
      (expI_smul_eq_self_of_moment_apply_le h hμ.toIsMomentMap hg
        (by rw [hfix, hy, hx])).symm.trans hfix
    rw [hux] at hfix
    refine ⟨not_not.1 fun hne ↦ ?_, hux⟩
    -- `expI (-η)` fixes `x`, so `⟨μ, η⟩` would be positive at `x`.
    have hpos := moment_expI_neg_smul_apply_pos h hμ.toIsMomentMap hg hx hne
    rw [C.expI_neg, inv_smul_eq_iff.2 hfix.symm, hx, LinearMap.zero_apply] at hpos
    exact lt_irrefl 0 hpos
  · simpa [hu] using h.expI_smul_smul_eq_self_iff.2 hX 1

end SymplecticGeometry
