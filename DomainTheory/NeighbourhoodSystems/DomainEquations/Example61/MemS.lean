/-ai
The neighbourhoods of the tree algebra are the least family of sets of path-token pairs that contains the master, contains the zero-tagged copy of every neighbourhood of the original system, and contains the union of the left-tagged copy of P and the right-tagged copy of Q whenever it contains both P and Q.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.Gamma

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- **Example 6.1 (Scott 1981, PRG-19).** The neighbourhoods of `D^§`, defined inductively as the
*least* family of subsets of `Γ` containing (i) `Γ`, (ii) `0X` for `X ∈ 𝒟`, and (iii) `1P ∪ 2Q`
whenever it already contains `P` and `Q`. This is Scott's fixed-point family
`𝒟^§ = {Γ} ∪ {0X ∣ X ∈ 𝒟} ∪ {1P ∪ 2Q ∣ P, Q ∈ 𝒟^§}`. -/
inductive MemS (D : NeighborhoodSystem α) : Set (List Bool × α) → Prop
  | gamma : MemS D (Gamma D)
  | zero {X : Set α} : D.mem X → MemS D (embZero X)
  | pair {P Q : Set (List Bool × α)} : MemS D P → MemS D Q → MemS D (embPair P Q)

end Example61
end DomainTheory.NeighbourhoodSystems
