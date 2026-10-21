/-ai
The positive meet-fold of a list has success bit at most one. Success means that the index set of the resulting index equals the positive index set of the list, and failure means that the positive index set is empty.

Instantiate the folded invariant at the initial accumulator pairing one with the master index and at the set of all indices. The initial success bit is one, its index is the master index, whose index set is everything, and the failure hypothesis on that initial accumulator is impossible. Cancelling the intersection with the set of all indices gives the claim.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.idxSet_masterIdx_eq_univ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.meetFold_foldl_spec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable (cons : ℕ → ℕ)


/-- **Correctness of the positive meet-fold**, instantiated at the real starting point
`(1, masterIdx)`/`Set.univ`. -/
theorem meetFold_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (pos : List ℕ) :
    (meetFold P cons pos).unpair.1 ≤ 1 ∧
      ((meetFold P cons pos).unpair.1 = 1 →
        idxSet P.X (meetFold P cons pos).unpair.2 = IPos P pos) ∧
      ((meetFold P cons pos).unpair.1 = 0 → IPos P pos = ∅) := by
  have hinit1 : (Nat.pair 1 P.masterIdx).unpair.1 = 1 := unpair_pair_fst 1 P.masterIdx
  have hinit2 : (Nat.pair 1 P.masterIdx).unpair.2 = P.masterIdx := unpair_pair_snd 1 P.masterIdx
  have h := meetFold_foldl_spec P cons hcons pos (init := Nat.pair 1 P.masterIdx) (S := Set.univ)
    (by rw [hinit1]) (fun _ => by rw [hinit2]; exact idxSet_masterIdx_eq_univ P)
    (fun h => absurd (hinit1.symm.trans h) (by norm_num))
  simpa only [meetFold, Set.univ_inter] using h

end DomainTheory.NeighbourhoodSystems
