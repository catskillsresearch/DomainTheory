module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_inter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

/-- **The positive `n`-fold product `Vⁿ`** of a neighbourhood system `V`, over `Fin n × β`.
The assumption `0 < n` is necessary because Scott's token set `Fin n × Δ` must be non-empty.
Its neighbourhoods are exactly the proper products `prodN X` with each component `X j ∈ V`;
closure under intersection is componentwise. -/
def npow (V : NeighborhoodSystem β) (n : ℕ) (hn : 0 < n) : NeighborhoodSystem (Fin n × β) where
  mem W := ∃ X : Fin n → Set β, (∀ j, V.mem (X j)) ∧ W = prodN X
  master := prodN (fun _ => V.master)
  master_nonempty := by
    obtain ⟨b, hb⟩ := V.master_nonempty
    exact ⟨(⟨0, hn⟩, b), hb⟩
  master_mem := ⟨_, fun _ => V.master_mem, rfl⟩
  inter_mem := by
    rintro W W' Z ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩ ⟨Zw, hZw, rfl⟩ hsub
    refine ⟨fun j => X j ∩ X' j, ?_, prodN_inter⟩
    intro j
    rw [prodN_inter] at hsub
    exact V.inter_mem (hX j) (hX' j) (hZw j) (prodN_subset.mp hsub j)
  sub_master := by
    rintro W ⟨X, hX, rfl⟩
    exact prodN_subset.mpr (fun j => V.sub_master (hX j))

end Example62A

end DomainTheory.NeighbourhoodSystems
