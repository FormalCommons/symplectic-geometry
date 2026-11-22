/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.FiberBundle.Pullback

/-!
# Maps into a pull-back bundle

For a map `f : X → B` and a bundle `V` over `B` with model fibre `F`, a family of maps
`φ y : F → V (f y)` defines a fibrewise map from the trivial bundle `Bundle.Trivial X F` to the
pull-back `f *ᵖ V`. This file shows that this map is continuous on total spaces as soon as the
family is continuous from `X × F` to the total space of `V`. This is how a frame of `V` along
`f` becomes a continuous fibrewise isomorphism onto the pull-back.

It also gives the pointwise form of Tau Ceti's `Bundle.Pullback.continuous_iff`: a map into the
total space of `f *ᵖ V` is continuous at a point exactly when its projection to the base and its
lift to the total space of `V` are. The proof is that of `Bundle.Pullback.continuous_iff`, with
`ContinuousAt` in place of `Continuous`.

## Main results

* `Bundle.Pullback.continuousAt_iff`: continuity at a point of a map into the total space of a
  pull-back bundle, through its projection and its lift.
* `Bundle.Pullback.continuous_totalSpaceMk_trivial`: a family of maps from the model fibre `F` to
  the fibres of `V` along `f : X → B`, continuous on `X × F`, is continuous from the trivial
  bundle `Bundle.Trivial X F` to the pull-back `f *ᵖ V`.
-/

public section

open Bundle

namespace Bundle.Pullback

variable {B F : Type*} {V : B → Type*} [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F V)] {X : Type*} [TopologicalSpace X]

omit [TopologicalSpace F] in
/-- A map `g` into the total space of a pull-back bundle `f *ᵖ V` is continuous at `z` exactly
when its projection to the base `X` and its lift to the total space of `V` are continuous at
`z`. -/
theorem continuousAt_iff {Z : Type*} [TopologicalSpace Z] {f : X → B}
    {g : Z → TotalSpace F (f *ᵖ V)} {z : Z} :
    ContinuousAt g z ↔
      ContinuousAt (fun z ↦ (g z).proj) z ∧ ContinuousAt (fun z ↦ Pullback.lift f (g z)) z :=
  (inducing_pullbackTotalSpaceEmbedding F V f).continuousAt_iff.trans (Prod.tendsto_iff _ _)

/-- A family of maps `φ y : F → V (f y)` along `f : X → B`, continuous as a map from `X × F` to
the total space of `V`, is continuous as a fibrewise map from the trivial bundle `X × F` to the
pull-back `f *ᵖ V`. -/
theorem continuous_totalSpaceMk_trivial {f : X → B} {φ : ∀ y, F → V (f y)}
    (hφ : Continuous fun q : X × F ↦ TotalSpace.mk' F (f q.1) (φ q.1 q.2)) :
    Continuous fun p : TotalSpace F (Trivial X F) ↦
      TotalSpace.mk' F (E := f *ᵖ V) p.proj (φ p.proj p.snd) :=
  Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj F _,
    hφ.comp (Trivial.homeomorphProd X F).continuous⟩

end Bundle.Pullback

end
