/-ai
The left branch, the right branch, and each of the four leaves are distinct from the master neighbourhood. The leaves 00 and 01 are distinct from the left branch, and the leaves 10 and 11 are distinct from the right branch.

If the left branch equalled the master neighbourhood, the token 0 would belong to the left branch, which it does not. The same token separates the right branch and each leaf from the master neighbourhood. The token 1 separates the leaves 00 and 01 from the left branch, and the token 2 separates the leaves 10 and 11 from the right branch.

The leaf 00 is contained in the left branch, the leaf 01 is contained in the left branch, the leaf 10 is contained in the right branch, and the leaf 11 is contained in the right branch.

Take a token of the leaf and case-split on the seven tokens. The leaf and branch definitions discharge the membership.

An element containing the leaf 00 equals the total element at 00, an element containing the leaf 01 equals the total element at 01, an element containing the leaf 10 equals the total element at 10, and an element containing the leaf 11 equals the total element at 11.

Upward closure supplies the left branch from 00 or 01, and the right branch from 10 or 11. Extensionality of elements reduces the equality to membership of a neighbourhood, which is one of the seven. The master neighbourhood, the relevant branch, and the given leaf are the three neighbourhoods of the total element. Each of the other four neighbourhoods meets the given leaf in the empty set, by case analysis on the tokens, so that intersection cannot belong to the element, because the empty set is not a neighbourhood. Conversely, the master neighbourhood belongs by the master axiom, the branch belongs by the upward step, and the leaf belongs by hypothesis.

An element that contains the left branch and neither leaf 00 nor leaf 01 equals the partial element at node 0. An element that contains the right branch and neither leaf 10 nor leaf 11 equals the partial element at node 1.

Extensionality classifies a neighbourhood of the element. The master neighbourhood and the given branch are the two neighbourhoods of the partial element. The opposite branch and the two leaves of the opposite branch meet the given branch in the empty set, by case analysis on the tokens, so they are excluded. The two leaves under the given branch are excluded by hypothesis. Conversely, the master neighbourhood belongs by the master axiom and the branch belongs by hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.memSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.neighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elemZero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elemOne
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elem00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elem01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elem10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.elem11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.Token
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.not_mem_empty
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.eq_of_master_subset
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_subset_cases
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.master_inter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_master
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.left_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_left
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.right_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf00_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf00
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf01_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf01
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf10_inter_leaf11
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.leaf11_inter_leaf10
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Example14.inter_eq

@[expose] public section

/-!
# Example 1.4 (Scott 1981, PRG-19, §1)

Scott's third worked example: the **binary tree** of depth 2. Tokens are the finite binary
sequences of length ≤ 2, `Δ = {Λ, 0, 1, 00, 01, 10, 11}`, and the neighbourhoods are the
subtrees rooted at each node:

`𝒟 = {Δ, {0,00,01}, {1,10,11}, {00}, {01}, {10}, {11}}`.

We encode the seven tokens as `Fin 7`:

| token | `Λ` | `0` | `1` | `00` | `01` | `10` | `11` |
| ----- | --- | --- | --- | ---- | ---- | ---- | ---- |
| `Fin 7` | `0` | `1` | `2` | `3` | `4` | `5` | `6` |

so `left = {0,00,01} = {1,3,4}`, `right = {1,10,11} = {2,5,6}`, and the four leaves are the
singletons `{3}, {4}, {5}, {6}`.

We build the neighbourhood system (Definition 1.1) and classify its domain elements
(Definition 1.6): there are exactly **seven** filters. Unlike Example 1.3's linear chain, this is
the first example with **branching** — at the partial elements `elemZero`/`elemOne` one has a
*choice* of how to refine toward one of the four total (leaf) elements.

This is a concrete finite computation (`fin_cases`/`simp`); footprint
`[propext, Classical.choice, Quot.sound]` — same as Examples 1.2/1.3.
-/

namespace DomainTheory.NeighbourhoodSystems.Example14


/-! ### Distinctness of neighbourhoods (only the pairs needed below). -/

theorem left_ne_master : left ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ left := by rw [h]; simp [master]
  simp [left] at hmem

theorem right_ne_master : right ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ right := by rw [h]; simp [master]
  simp [right] at hmem

theorem leaf00_ne_master : leaf00 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf00 := by rw [h]; simp [master]
  simp [leaf00] at hmem

theorem leaf01_ne_master : leaf01 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf01 := by rw [h]; simp [master]
  simp [leaf01] at hmem

theorem leaf10_ne_master : leaf10 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf10 := by rw [h]; simp [master]
  simp [leaf10] at hmem

theorem leaf11_ne_master : leaf11 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf11 := by rw [h]; simp [master]
  simp [leaf11] at hmem

theorem leaf00_ne_left : leaf00 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf00 := by rw [h]; simp [left]
  simp [leaf00] at hmem

theorem leaf01_ne_left : leaf01 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf01 := by rw [h]; simp [left]
  simp [leaf01] at hmem

theorem leaf10_ne_right : leaf10 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf10 := by rw [h]; simp [right]
  simp [leaf10] at hmem

theorem leaf11_ne_right : leaf11 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf11 := by rw [h]; simp [right]
  simp [leaf11] at hmem

/-! ### Nested-subset facts. -/

theorem leaf00_subset_left : leaf00 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf00, left] at ht ⊢

private theorem leaf01_subset_left : leaf01 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf01, left] at ht ⊢

private theorem leaf10_subset_right : leaf10 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf10, right] at ht ⊢

private theorem leaf11_subset_right : leaf11 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf11, right] at ht ⊢

/-! ### "Which neighbourhoods contain a given one" (upward classification). -/


/-! ### Intersections. -/


namespace neighborhoodSystem

open NeighborhoodSystem


/-! ### Filter classification: the seven elements. -/

theorem mem_leaf00_imp (x : neighborhoodSystem.Element) (h : x.mem leaf00) :
    x = elem00 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf00_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

theorem mem_leaf01_imp (x : neighborhoodSystem.Element) (h : x.mem leaf01) :
    x = elem01 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf01_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

theorem mem_leaf10_imp (x : neighborhoodSystem.Element) (h : x.mem leaf10) :
    x = elem10 := by
  have hright : x.mem right := x.up_mem h mem_right leaf10_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

theorem mem_leaf11_imp (x : neighborhoodSystem.Element) (h : x.mem leaf11) :
    x = elem11 := by
  have hright : x.mem right := x.up_mem h mem_right leaf11_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

theorem mem_left_imp (x : neighborhoodSystem.Element) (hl : x.mem left)
    (h00 : ¬x.mem leaf00) (h01 : ¬x.mem leaf01) : x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ right : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, right]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h00
    · exact absurd hx h01
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hl

theorem mem_right_imp (x : neighborhoodSystem.Element) (hr : x.mem right)
    (h10 : ¬x.mem leaf10) (h11 : ¬x.mem leaf11) : x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ left : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, left]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hr

/-! ### The approximation order (Definition 1.8): a branching tree. -/
end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
