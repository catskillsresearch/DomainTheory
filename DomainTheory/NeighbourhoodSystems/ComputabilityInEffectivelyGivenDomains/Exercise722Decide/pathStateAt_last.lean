module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable {σ : Type}


section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}


omit [Fintype σ] in
theorem pathStateAt_last {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p x.length (Nat.le_refl _) = t := by
  induction p with
  | nil s => simp [pathStateAt, pathStateAtAux]
  | cons sMid s' u a xs hstep p' ih =>
    simp [pathStateAt, pathStateAtAux, List.length_cons]
    exact ih

end ShortWord
end Exercise722
end DomainTheory.NeighbourhoodSystems
