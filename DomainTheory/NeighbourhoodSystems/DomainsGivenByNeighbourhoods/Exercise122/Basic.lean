/-ai
The basic open of an intersection is contained in the basic open of the left factor whenever that factor is a neighbourhood.

A filter containing the intersection contains the left factor by upward closure along the left inclusion.

The basic open of an intersection is contained in the basic open of the right factor whenever that factor is a neighbourhood.

A filter containing the intersection contains the right factor by upward closure along the right inclusion.

The elements carry the topology whose open sets are the open filters. The whole space is open because every element contains the master and the basic open of the master is contained in the whole space. The intersection of two open sets is open because a common point has a basic neighbourhood inside each, and the basic open of the intersection of those neighbourhoods is contained in both. A union of open sets is open because a point of the union lies in some member, and a basic neighbourhood of that point inside the member is contained in the union.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Topology.Inseparable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.basicOpen
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.OpenFilter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise122.mem_basicOpen

@[expose] public section

/-!
# Exercise 1.22 (Scott 1981, PRG-19, §1) — the topology on `|𝒟|`

> **EXERCISE 1.22.** (For topologists). Show that the neighbourhoods `[X]` for `X ∈ 𝒟` make
> `|𝒟|` into a topological space where the open subsets `𝒰 ⊆ |𝒟|` can be characterized by the
> following two conditions:
>
> (i)  whenever `x ∈ 𝒰` and `x ⊑ y ∈ |𝒟|`, then `y ∈ 𝒰`; and
> (ii) whenever `x ∈ 𝒰`, then `[X] ⊆ 𝒰` for some `X ∈ x`.
>
> Prove also that the inclusion relation on `|𝒟|` can be defined topologically as:
>
> (iii) `x ⊑ y` iff for all open `𝒰 ⊆ |𝒟|`, if `x ∈ 𝒰` then `y ∈ 𝒰`.

Here `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Scott's notation from Theorem 1.10): the set of elements
(filters) of which `X` is a member. We call it `basicOpen X`.

## What is proved

* `basicOpen` — Scott's `[X]`, with `mem_basicOpen` the membership unfolding.
* `instTopologicalSpaceElement` — the topology on `V.Element`: `𝒰` is open iff every point of
  `𝒰` has a basic neighbourhood `[X]` (`X ∈ x`) contained in `𝒰`. This is condition (ii); the
  three topology axioms are verified directly (the basic opens are closed under finite `∩`, with
  `[Δ] = |𝒟|` the whole space, so they form a base).
* `isOpen_basicOpen` — each `[X]` is open.
* `isOpen_iff_upper_basic` — the characterization: `IsOpen 𝒰 ↔ (i) ∧ (ii)`. Note (ii) already
  pins down openness; (i) (upward closure under `⊑`) is a *consequence* of (ii), recorded
  separately as `isOpen_isUpperSet`. We keep both to match Scott's statement.
* `le_iff_isOpen_imp` — condition (iii): `x ⊑ y ↔ ∀ 𝒰 open, x ∈ 𝒰 → y ∈ 𝒰`. This says `⊑` is
  the (opposite of the) specialization preorder; `specializes_iff_le` makes the bridge to
  Mathlib's `⤳` explicit.

The space is **T₀** but not in general **T₁**/Hausdorff (the specialization order `⊑` is a genuine
partial order, recoverable from the topology by (iii)); the open-ended limit-point questions of the
exercise need Definition 1.7 (`↑X`) and are deferred.
-/

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `[X ∩ Y] ⊆ [X]` whenever `X ∈ 𝒟`: a filter containing `X ∩ Y` contains `X` (upward closure).
This (with the symmetric version) is the closure of the basic opens under finite intersection,
i.e. `[X] ∩ [Y] = [X ∩ Y]`, the base condition behind the topology. -/
theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

/-- `[X ∩ Y] ⊆ [Y]` whenever `Y ∈ 𝒟`. -/
theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right


/-- **Exercise 1.22 (the space).** The basic opens `[X]` (`X ∈ 𝒟`) generate a topology on `|𝒟|`:
`𝒰` is open iff it is a union of basic opens (condition (ii)). The three axioms hold because the
base is closed under finite intersection (`basicOpen_inter_subset_left/right`, using that filters
are `∩`-closed and upward closed) with `[Δ] = |𝒟|` covering the space. -/
instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.OpenFilter
  isOpen_univ := ⟨fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩⟩
  isOpen_inter := by
    intro U W hU hW
    constructor
    intro x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU.out x hxU
    obtain ⟨Y, hY, hYW⟩ := hW.out x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS
    constructor
    intro x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := (hS t htS).out x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
