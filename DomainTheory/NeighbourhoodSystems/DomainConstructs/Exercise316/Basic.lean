module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSeqEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.natShiftEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterProdIso
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.projN
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_fiber
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.eq_of_fiber_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_self
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_single_ne
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.fiber_iterSys_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_iterSys
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.single_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.subset_single
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.interUpTo_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.reconstruct_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.mem_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.component_ofSeq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.ofSeq_component
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.le_of_component_le

@[expose] public section

/-!
# Exercise 3.16 (Scott 1981, PRG-19, §3) — the infinite iterate `𝒟^∞`

Scott: for a neighbourhood system `𝒟` over `Δ`, let `Δ^∞ = ⋃ₙ 1ⁿ0Δ` be infinitely many disjoint
copies of `Δ`, and let `𝒟^∞` be the *least* family of subsets with

1. `Δ^∞ ∈ 𝒟^∞`, and
2. `X ∈ 𝒟`, `Y ∈ 𝒟^∞` ⟹ `0X ∪ 1Y ∈ 𝒟^∞`.

He asks to show `𝒟^∞` is a neighbourhood system over `Δ^∞`, that `𝒟^∞ ≅ 𝒟 × 𝒟^∞`, and that the
elements of `|𝒟^∞|` are in one-one correspondence with arbitrary infinite sequences `⟨xₙ⟩` of
elements `xₙ ∈ |𝒟|`, via the combinations of neighbourhoods

`0X₀ ∪ 10X₁ ∪ ⋯ ∪ 1ⁿ0Xₙ ∪ ⋯`   (with all but finitely many `Xₘ = Δ`).

**Model.** We take the token type to be `ℕ × α`, where `(n, a)` is "the token `a ∈ Δ` sitting in
the `n`-th copy" (i.e. Scott's `1ⁿ0a`). A neighbourhood `0X₀ ∪ 1ⁿ0Xₙ ∪ ⋯` is then exactly the set
`{(i, a) ∣ a ∈ Xᵢ}`, recovered from `W` by its **fibers** `fiber W i = {a ∣ (i, a) ∈ W}`. The
"least family" description is equivalent to: `W ∈ 𝒟^∞` iff every fiber is a neighbourhood and all
but finitely many fibers equal `Δ`. (Closure under (2) and the base (1) generate exactly these, and
no fewer, because (2) is the one-step "cons" and the cofinite-`Δ` condition is its iterate.)

The element-level payoff is the clean order-isomorphism

`iterSeqEquiv : |𝒟^∞| ≃o (ℕ → |𝒟|)`

(Scott's "one-one correspondence with infinite sequences"), from which `𝒟^∞ ≅ 𝒟 × 𝒟^∞` falls out by
the shift `(ℕ → E) ≃o E × (ℕ → E)`.

Everything is **choice-free in spirit**; the classical content is only what is inherited from the
project's `Element.ext`/`prodEquiv` machinery, as elsewhere in §3.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-! ### Fibers of a set of `(copy index, token)` pairs. -/






theorem subset_of_fiber_subset {W W' : Set (ℕ × α)} (h : ∀ i, fiber W i ⊆ fiber W' i) :
    W ⊆ W' := fun ⟨i, _⟩ ha => h i ha

/-! ### The pinning neighbourhood `single n X` (Scott's `1ⁿ0X`, rest `Δ`). -/

variable (V : NeighborhoodSystem α)


variable {V}





/-! ### The system `𝒟^∞`. -/










/-! ### Components and sequences. -/






/-! ### The two round-trips. -/




/-! ### Scott's two conclusions. -/




/-! ### The coordinate projections `𝒟^∞ → 𝒟` (used in Exercise 3.24(ii)). -/

open ApproximableMap


@[simp] theorem projN_rel {n : ℕ} {W : Set (ℕ × α)} {X : Set α} :
    (projN V n).rel W X ↔ (iterSys V).mem W ∧ V.mem X ∧ fiber W n ⊆ X := Iff.rfl

@[simp] theorem toElementMap_projN (z : (iterSys V).Element) (n : ℕ) :
    (projN V n).toElementMap z = component z n := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨W, hzW, hW, hX, hsub⟩
    refine ⟨hX, z.up_mem hzW (single_mem hX) ?_⟩
    refine subset_of_fiber_subset (fun i => ?_)
    by_cases h : i = n
    · subst h; rw [fiber_single_self]; exact hsub
    · rw [fiber_single_ne h]; exact V.sub_master (hW.1 i)
  · rintro ⟨hX, hz⟩
    exact ⟨single V n X, hz, single_mem hX, hX, by rw [fiber_single_self]⟩
end DomainTheory.NeighbourhoodSystems
