/-ai
If the zero-embedding of a set X is a neighbourhood of D-sharp, then X is a neighbourhood of D.

The construction cannot be the master: a point of the master of D whose boolean list is true followed by the empty list lies in the master of D-sharp but not in a zero-embedding. A zero-copy reduces by injectivity of the zero-embedding. A pair-copy is impossible: a point of a nonempty pair embedding has a nonempty boolean list, while every point of a zero-embedding has an empty list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

theorem memS_embZero_inv {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α}
    (h : MemS D (embZero X)) : D.mem X := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma =>
    exfalso
    obtain ⟨a, ha⟩ := hD D.master D.master_mem
    have h1 : ((true :: [], a) : List Bool × α) ∈ Gamma D := ha
    rw [← hW] at h1; exact absurd h1.1 (by simp)
  | @zero X' hX' => rw [embZero_injective hW]; exact hX'
  | @pair P Q hP hQ =>
    exfalso
    obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
    have hcons : t.1 ≠ [] := by
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp [hp']
      · simp [hq']
    have hz : t ∈ embZero X := by rw [← hW] at ht; exact ht
    exact hcons hz.1

end Example61

end DomainTheory.NeighbourhoodSystems
