/-ai
If interpreting every entry of a list of natural numbers as a boolean yields a list of booleans, then the original list is that list of booleans mapped by the boolean-to-natural encoding.

Induction on the list. The empty list forces the boolean list to be empty. A cons cell splits the mapped option: a failed head or tail is impossible, and a successful head and tail identify the boolean list as that boolean followed by the tail list. The inductive hypothesis rewrites the tail, and a successful boolean interpretation means the head equals the encoding of that boolean.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.boolNat
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool_eq_some_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

theorem mapM_natBool_eq_some (l : List ℕ) (σ : List Bool)
    (h : l.mapM natBool = some σ) : l = σ.map boolNat := by
  induction l generalizing σ with
  | nil => rw [List.mapM_nil] at h; simpa using h.symm
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hnx : natBool x with
    | none => simp [hnx] at h
    | some b =>
      cases htx : xs.mapM natBool with
      | none => simp [hnx, htx] at h
      | some ys =>
        simp only [hnx, htx] at h
        obtain rfl : σ = b :: ys := by simpa using h.symm
        simp [ih ys htx, (natBool_eq_some_iff x b).mp hnx]

end Exercise722

end DomainTheory.NeighbourhoodSystems
