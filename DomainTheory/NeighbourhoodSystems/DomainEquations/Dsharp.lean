/-ai
The tree algebra of a neighbourhood system whose neighbourhoods are all nonempty is the neighbourhood system on pairs of a finite boolean path and a token, with neighbourhoods the inductive tree-algebra family and with master the set of pairs whose token lies in the original master. A token of that master paired with the empty path shows the master nonempty, the master belongs to the inductive family, intersections of members remain members by the intersection lemma for the family, and every member is contained in the master.
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_inter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 (Scott 1981, PRG-19).** The *tree algebra* `D^§`: a neighbourhood system over
`Γ = {1,2}* 0 Δ`, under the standing assumption `∅ ∉ 𝒟` (`hD`). -/
abbrev Dsharp (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty) :
    NeighborhoodSystem (List Bool × α) where
  mem := MemS D
  master := Gamma D
  master_nonempty := by
    obtain ⟨a, ha⟩ := D.master_nonempty
    exact ⟨([], a), ha⟩
  master_mem := MemS.gamma
  inter_mem := fun hX hY hZ hsub => memS_inter hD hX hY hZ hsub
  sub_master := memS_subset_gamma

end Example61

end DomainTheory.NeighbourhoodSystems
