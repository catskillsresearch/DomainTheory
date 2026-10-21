/-ai
The cone of a finite bit string lies on the branch of an infinite path exactly when the string is a prefix of some finite initial segment of the path.

In the forward direction, the union lemma for the monotone branch sequence supplies an index whose cone contains the cone of the string, and that cone inclusion is a prefix. In the reverse direction, the same union lemma is applied to the cone of the string, which is a neighbourhood, together with the cone inclusion coming from the prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB








/-- `cone σ ∈ branch p` iff `σ` is an initial segment of some `p ↾ n`, i.e. `σ` lies on the path. -/
theorem branch_mem_iff (p : ℕ → Bool) {σ : Str} :
    (branch p).mem (cone σ) ↔ ∃ n, σ <+: prefixSeq p n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mp h
    exact ⟨n, cone_subset_cone.mp hn.2⟩
  · rintro ⟨n, hn⟩
    exact (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mpr
      ⟨n, memB_cone σ, cone_subset_cone.mpr hn⟩

end DomainTheory.NeighbourhoodSystems.Exercise113
