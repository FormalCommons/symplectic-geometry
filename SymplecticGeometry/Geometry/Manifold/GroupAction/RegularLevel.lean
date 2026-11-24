/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Restrict
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Topology.Algebra.ProperAction.Basic
public import SymplecticGeometry.Geometry.Manifold.GroupAction.PrincipalBundle

/-!
# The circle bundle of a regular level

Let a commutative Lie group `G`, such as `Circle`, act smoothly on a boundaryless manifold `M`,
and let `f : M → F` be a smooth `G`-invariant map with regular value `c`. The level
`{x // f x = c}` carries Tau Ceti's atlas `TauCeti.regularLevelChartedSpace`. This file restricts
the action to the level, written as a right action as principal bundles in Tau Ceti act: since
`G` is commutative, `op g • x = g • x` is an action of `Gᵐᵒᵖ`
(`SymplecticGeometry.levelOpMulAction`). The restricted action is

* smooth for the regular-level atlas (`SymplecticGeometry.contMDiffSMul_levelOpMulAction`), as
  the inclusion of the level is a smooth embedding
  (`TauCeti.isSmoothEmbedding_coe_regularLevel`), by
  `Manifold.IsSmoothEmbedding.contMDiffSMul`;
* free when `G` acts freely at the points of the level
  (`SymplecticGeometry.isCancelSMul_levelOpMulAction`);
* proper when `G` is compact and `M` Hausdorff
  (`SymplecticGeometry.properSMul_levelOpMulAction`, by `TauCeti.properSMul_of_compactSpace`).

These are the hypotheses of `GroupAction/PrincipalBundle.lean`, so the orbits of the level form a
smooth principal `G`-bundle `orbitFiber Gᵐᵒᵖ {x // f x = c}` over the orbit space, and Tau Ceti's
`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph` identifies its total space with the level,
equivariantly and over the orbit projection. The orbit space is Hausdorff (Mathlib's
`t2Space_quotient_mulAction_of_properSMul`), compact when the level is, and a boundaryless
finite-dimensional manifold modelled on `ProperSMul.QuotientModelSpace`; so it is a base as in
`Geometry/Symplectic/Coupling/Basic.lean`. The example at the end of the file checks this.

**Local instances.** None of these structures is a global instance: the action depends on the
proof of invariance, the atlases on the models and on the regularity proofs. A statement about
the bundle of a level, such as the converse of minimal coupling, puts them in place in this
order, with `attribute [local instance] MulOpposite.chartedSpace` for the charts of `G` on `Gᵐᵒᵖ`
and `P₀ = {x // f x = c}`:

* `letI := TauCeti.regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le (by simp)) hreg hn`
  and `letI := SymplecticGeometry.levelOpMulAction c hinv`, the atlas and the action on `P₀`;
* `haveI` for `TauCeti.isManifold_regularLevel (by simp) hf hreg hn`,
  `contMDiffSMul_levelOpMulAction (by simp) hf hreg hn hinv`, `ContMDiffSMul.continuousSMul`,
  `properSMul_levelOpMulAction` and `isCancelSMul_levelOpMulAction`;
* then those of `GroupAction/PrincipalBundle.lean`:
  `letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ) P₀`,
  `letI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) P₀).fiberBundle`,
  `haveI := orbitFiber.principalBundle IG G 𝓘(ℝ, Fin n → ℝ) P₀` and
  `haveI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) P₀).contMDiffFiberBundle
    (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) P₀)`.

Here `hf` is the smoothness of `f`, at order `∞`, at the points of the level, as in
`TauCeti.isManifold_regularLevel`; the regular-level atlas takes it at order `1`.

## Main definitions and results

* `SymplecticGeometry.levelOpMulAction`: the right action of a commutative group on a level of an
  invariant map, with `SymplecticGeometry.coe_levelOpMulAction_smul`.
* `SymplecticGeometry.continuousSMul_levelOpMulAction`, `contMDiffSMul_levelOpMulAction`: it is
  continuous, and smooth for the regular-level atlas.
* `SymplecticGeometry.isCancelSMul_levelOpMulAction`: it is free where `G` acts freely.
* `SymplecticGeometry.properSMul_levelOpMulAction`: it is proper for compact `G`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.1
  (the circle bundle of a regular level of a free circle action, in minimal coupling).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Theorem 21.10 (the quotient manifold
  theorem).
-/

public section

open MulAction MulOpposite TauCeti
open scoped ContDiff Manifold

namespace SymplecticGeometry

/-! ### The right action on a level -/

section Action

variable {G M F : Type*} [CommGroup G] [MulAction G M] {f : M → F}

variable (c : F) in
/-- The right action of a commutative group `G` on a level `{x // f x = c}` of a `G`-invariant
map `f`, written as an action of `Gᵐᵒᵖ`: `op g` moves `x` to `g • x`. -/
@[instance_reducible]
def levelOpMulAction (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    MulAction Gᵐᵒᵖ {x : M // f x = c} where
  smul g x := ⟨unop g • (x : M), (hinv _ _).trans x.property⟩
  one_smul x := Subtype.ext (one_smul G (x : M))
  mul_smul g h x := Subtype.ext <| by
    -- The goal is stated with the `smul` field being defined; `change` reads it on `M`.
    change unop (g * h) • (x : M) = unop g • unop h • (x : M)
    rw [unop_mul, mul_comm, mul_smul]

variable (hinv : ∀ (g : G) (x : M), f (g • x) = f x) {c : F}

/-- The action `levelOpMulAction` is the action of `G` on `M`, read through `unop`. -/
@[simp]
theorem coe_levelOpMulAction_smul (g : Gᵐᵒᵖ) (x : {x : M // f x = c}) :
    letI := levelOpMulAction c hinv
    ((g • x : {x : M // f x = c}) : M) = unop g • (x : M) :=
  (rfl)

/-- **Freeness on the level.** If `G` acts freely at every point of the level, then `Gᵐᵒᵖ` acts
freely on it. -/
theorem isCancelSMul_levelOpMulAction (hfree : ∀ x, f x = c → stabilizer G x = ⊥) :
    letI := levelOpMulAction c hinv
    IsCancelSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  isCancelSMul_iff_stabilizer_eq_bot.2 fun x ↦ (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ by
    have hg' : unop g ∈ stabilizer G (x : M) := by
      rw [mem_stabilizer_iff, ← coe_levelOpMulAction_smul hinv, (mem_stabilizer_iff).1 hg]
    rw [hfree x x.property, Subgroup.mem_bot] at hg'
    rw [← op_unop g, hg', op_one]

variable [TopologicalSpace G] [TopologicalSpace M] [ContinuousSMul G M]

/-- The action `levelOpMulAction` is continuous, for the subspace topology of the level. -/
theorem continuousSMul_levelOpMulAction :
    letI := levelOpMulAction c hinv
    ContinuousSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  ⟨((continuous_unop.comp continuous_fst).smul
    (continuous_subtypeVal.comp continuous_snd)).subtype_mk _⟩

/-- **Properness on the level.** A compact group acts properly on a level of an invariant map in a
Hausdorff space. -/
theorem properSMul_levelOpMulAction [CompactSpace G] [T2Space M] :
    letI := levelOpMulAction c hinv
    ProperSMul Gᵐᵒᵖ {x : M // f x = c} :=
  letI := levelOpMulAction c hinv
  haveI := continuousSMul_levelOpMulAction (c := c) hinv
  properSMul_of_compactSpace Gᵐᵒᵖ _

end Action

/-! ### Smoothness on a regular level -/

section Smooth

attribute [local instance] MulOpposite.chartedSpace

variable {𝕜 : Type*} [RCLike 𝕜] {m : ℕ∞ω}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [CommGroup G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [MulAction G M] [ContMDiffSMul IG I m G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {f : M → F} {c : F} {n : ℕ}

/-- **The action on a regular level is `C^m`.** Let `1 ≤ m`. For the regular-level atlas of
`{x // f x = c}` and the charts of `G` on `Gᵐᵒᵖ`, the right action `levelOpMulAction` of a
commutative group `G` acting `C^m` on `M` is `C^m`. -/
theorem contMDiffSMul_levelOpMulAction (hm : 1 ≤ m)
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(𝕜, F) m f x)
    (hreg : IsRegularValue I 𝓘(𝕜, F) f c) (hn : Module.finrank 𝕜 E - Module.finrank 𝕜 F = n)
    (hinv : ∀ (g : G) (x : M), f (g • x) = f x) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
    letI := levelOpMulAction c hinv
    ContMDiffSMul IG 𝓘(𝕜, Fin n → 𝕜) m Gᵐᵒᵖ {x : M // f x = c} :=
  letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le hm) hreg hn
  letI := levelOpMulAction c hinv
  (isSmoothEmbedding_coe_regularLevel hm hf hreg hn).contMDiffSMul
    (contMDiff_unop IG m) fun g x ↦ coe_levelOpMulAction_smul hinv g x

end Smooth

/-! ### The principal bundle of a regular level -/

section Bundle

attribute [local instance] MulOpposite.chartedSpace

/- For a smooth action of a compact commutative Lie group `G` on a boundaryless Hausdorff
finite-dimensional manifold `M`, free on a regular level `P₀` of a smooth invariant map, the
local instances of the module docstring make the orbits of `P₀` a smooth principal `G`-bundle over
a Hausdorff boundaryless finite-dimensional manifold, compact when `P₀` is, whose total space is
diffeomorphic to `P₀`, equivariantly and over the orbit projection. -/
example
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [CommGroup G] [LieGroup IG ∞ G]
    [ContinuousInv G] [CompactSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MulAction G M] [ContMDiffSMul IG I ∞ G M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : M → F} {c : F} {n : ℕ}
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) ∞ f x) (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (hn : Module.finrank ℝ E - Module.finrank ℝ F = n)
    (hinv : ∀ (g : G) (x : M), f (g • x) = f x) (hfree : ∀ x, f x = c → stabilizer G x = ⊥) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le (by simp)) hreg hn
    letI := levelOpMulAction c hinv
    haveI := isManifold_regularLevel (by simp) hf hreg hn
    haveI := contMDiffSMul_levelOpMulAction (by simp) hf hreg hn hinv (IG := IG)
    haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
    haveI := properSMul_levelOpMulAction (c := c) hinv
    haveI := isCancelSMul_levelOpMulAction hinv hfree
    letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}
    letI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}).fiberBundle
    haveI := orbitFiber.principalBundle IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}
    haveI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}).contMDiffFiberBundle
      (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c})
    PrincipalBundle G (orbitFiber Gᵐᵒᵖ {x : M // f x = c}) ∧
      ContMDiffFiberBundle ∞ G (orbitFiber Gᵐᵒᵖ {x : M // f x = c})
        𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) IG ∧
      IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∞
        (orbitRel.Quotient Gᵐᵒᵖ {x : M // f x = c}) ∧
      (𝓘(ℝ, ProperSMul.QuotientModelSpace EG (Fin n → ℝ))).Boundaryless ∧
      FiniteDimensional ℝ (ProperSMul.QuotientModelSpace EG (Fin n → ℝ)) ∧
      T2Space (orbitRel.Quotient Gᵐᵒᵖ {x : M // f x = c}) ∧
      (CompactSpace {x : M // f x = c} →
        CompactSpace (orbitRel.Quotient Gᵐᵒᵖ {x : M // f x = c})) ∧
      ∀ (g : Gᵐᵒᵖ)
        (p : ManifoldTotalSpace G (orbitFiber Gᵐᵒᵖ {x : M // f x = c})),
        (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) _).totalSpaceDiffeomorph
            (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) _) (g • p) =
          g • (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) _).totalSpaceDiffeomorph
            (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) _) p ∧
        Quotient.mk _ ((orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) _).totalSpaceDiffeomorph
            (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) _) p) =
          ((ManifoldTotalSpace.homeomorph G _).symm p).proj :=
  letI := regularLevelChartedSpace (fun x hx ↦ (hf x hx).of_le (by simp)) hreg hn
  letI := levelOpMulAction c hinv
  haveI := isManifold_regularLevel (by simp) hf hreg hn
  haveI := contMDiffSMul_levelOpMulAction (by simp) hf hreg hn hinv (IG := IG)
  haveI := ContMDiffSMul.continuousSMul (I := IG) (I' := I) (G := G) (M := M) ∞
  haveI := properSMul_levelOpMulAction (c := c) hinv
  haveI := isCancelSMul_levelOpMulAction hinv hfree
  letI := ProperSMul.orbitRelQuotientChartedSpace IG Gᵐᵒᵖ 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}
  letI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}).fiberBundle
  haveI := orbitFiber.principalBundle IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}
  haveI := (orbitFiber.atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c}).contMDiffFiberBundle
    (orbitFiber.isContMDiff_atlas IG G 𝓘(ℝ, Fin n → ℝ) {x : M // f x = c})
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun _ ↦ inferInstance,
    fun g p ↦ ⟨MapFiber.Atlas.totalSpaceDiffeomorph_smul (a := g) (x := p)
      (hproj := fun _ _ ↦ orbitRel.Quotient.quotient_smul_eq) _,
      MapFiber.Atlas.proj_totalSpaceDiffeomorph (x := p) _⟩⟩

end Bundle

end SymplecticGeometry

end
