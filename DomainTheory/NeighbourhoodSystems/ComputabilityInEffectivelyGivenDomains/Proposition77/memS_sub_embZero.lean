/-ai
If a set in the sharp family is contained in a leaf embedding, then it is itself the leaf embedding of a neighbourhood of D.

On the master, nonemptiness supplies a point with a nonempty path, which cannot lie in a leaf embedding. On a leaf, the same neighbourhood is the witness. On a pair, nonemptiness of an embedded pair supplies a point whose path is nonempty, which cannot lie in a leaf embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem memS_sub_embZero (hD : ∀ X, D.mem X → X.Nonempty) {W : Set (List Bool × α)} {Y : Set α}
    (hW : MemS D W) (hsub : W ⊆ embZero Y) : ∃ Z, D.mem Z ∧ W = embZero Z := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      exact absurd (hsub (show ((true :: [], a) : List Bool × α) ∈ Gamma D from ha)).1 (by simp)
  | @zero Z hZ => exact ⟨Z, hZ, rfl⟩
  | @pair Pp Qq hP hQ =>
      obtain ⟨⟨pth, a⟩, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Qq)
      have hmem := hsub ht
      rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · exact absurd (hp'.symm.trans hmem.1) (by simp)
      · exact absurd (hq'.symm.trans hmem.1) (by simp)

end Proposition77

end DomainTheory.NeighbourhoodSystems
