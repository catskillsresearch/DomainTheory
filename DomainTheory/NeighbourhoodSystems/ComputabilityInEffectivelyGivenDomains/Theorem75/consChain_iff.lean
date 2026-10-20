/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)







section ConsChain

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)








/-- **Consistency via the `inter`-chain (choice-free).** A finite index set `js` is consistent — i.e.
`⋂{X_j ∣ j ∈ js}` is a neighbourhood — exactly when the always-a-neighbourhood `X_{idxchain js}` sits
inside every `X_j` (`j ∈ js`). -/
theorem consChain_iff (js : List ℕ) :
    (∀ j ∈ js, P.X (idxchain P js) ⊆ P.X j) ↔ V.mem (interFrom P V.master js) := by
  constructor
  · intro hle
    have hsub : P.X (idxchain P js) ⊆ interFrom P V.master js := by
      intro z hz
      rw [mem_interFrom]
      exact ⟨V.sub_master (P.mem_X _) hz, fun j hj => hle j hj hz⟩
    exact interFrom_mem_of_witness P (P.mem_X _) hsub V.master_mem
  · intro hmem j hj
    rw [idxchain_spec P hmem]
    exact fun z hz => (mem_interFrom P |>.mp hz).2 j hj

end ConsChain
end DomainTheory.NeighbourhoodSystems
