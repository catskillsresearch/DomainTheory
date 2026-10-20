/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise720.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*}



/-- **Exercise 7.20 — Scott's displayed formula.** On generators (nested finite lists of down-sets)
`(union).rel (⋃_{l∈LS} ↓_{ℙD}(⋃_{X∈l} ↓X)) (⋃_{Y∈LY} ↓Y) ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y`,
exactly Scott's `∀ i<n ∀ j<m_i ∃ k<q. X_{ij} ⊆ Y_k`. (`→` reads off the generators `X_{ij}`; `←`
extends to all members by downward closure at both levels and `⊆`-monotonicity of the target.) -/
theorem unionMap_rel_fin (V : NeighborhoodSystem α) {LS : List (List (Set α))} {LY : List (Set α)}
    (hLS : ∀ l ∈ LS, ∀ X ∈ l, V.mem X) (hLY : ∀ Y ∈ LY, V.mem Y) :
    (unionMap V).rel (⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X)) (⋃ Y ∈ LY, V.upSet Y)
      ↔ ∀ l ∈ LS, ∀ X ∈ l, ∃ Y ∈ LY, X ⊆ Y := by
  constructor
  · rintro ⟨-, -, hbody⟩ l hl X hX
    have hXmem : V.mem X := hLS l hl X hX
    have hSinA : (⋃ X ∈ l, V.upSet X) ∈ ⋃ l ∈ LS, V.PowerDomain.upSet (⋃ X ∈ l, V.upSet X) :=
      Set.mem_iUnion₂.mpr ⟨l, hl, (⟨l, hLS l hl, rfl⟩ : V.PDmem _), subset_rfl⟩
    have hXinS : X ∈ ⋃ X' ∈ l, V.upSet X' := (V.mem_PDunion).mpr ⟨X, hX, hXmem, subset_rfl⟩
    obtain ⟨Y, hYB, hXY⟩ := hbody _ hSinA X hXinS
    obtain ⟨Y', hY', hYin⟩ := (V.mem_PDunion).mp hYB
    exact ⟨Y', hY', hXY.trans hYin.2⟩
  · intro hgen
    refine ⟨?_, ⟨LY, hLY, rfl⟩, ?_⟩
    · refine ⟨LS.map (fun l => ⋃ X ∈ l, V.upSet X), ?_, ?_⟩
      · intro S hS
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hS
        exact ⟨l, hLS l hl, rfl⟩
      · ext z
        simp only [Set.mem_iUnion, List.mem_map, exists_prop]
        constructor
        · rintro ⟨l, hl, hz⟩
          exact ⟨_, ⟨l, hl, rfl⟩, hz⟩
        · rintro ⟨S, ⟨l, hl, rfl⟩, hz⟩
          exact ⟨l, hl, hz⟩
    · intro S hS X hX
      obtain ⟨l, hl, hSin⟩ := Set.mem_iUnion₂.mp hS
      have hXin : X ∈ ⋃ X' ∈ l, V.upSet X' := hSin.2 hX
      obtain ⟨X', hX', hXmem⟩ := (V.mem_PDunion).mp hXin
      obtain ⟨Y, hY, hX'Y⟩ := hgen l hl X' hX'
      exact ⟨Y, (V.mem_PDunion).mpr ⟨Y, hY, hLY Y hY, subset_rfl⟩, hXmem.2.trans hX'Y⟩

end DomainTheory.NeighbourhoodSystems
