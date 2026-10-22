module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem memS_sub_embPair (hD : ∀ X, D.mem X → X.Nonempty)
    {W A B : Set (List Bool × α)} (hW : MemS D W) (hsub : W ⊆ embPair A B) :
    ∃ Pp Qq, MemS D Pp ∧ MemS D Qq ∧ W = embPair Pp Qq := by
  cases hW with
  | gamma =>
      obtain ⟨a, ha⟩ := hD D.master D.master_mem
      rcases hsub (show (([], a) : List Bool × α) ∈ Gamma D from ha) with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @zero Z hZ =>
      obtain ⟨a, ha⟩ := hD Z hZ
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero Z from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  | @pair Pp Qq hP hQ => exact ⟨Pp, Qq, hP, hQ, rfl⟩

end Proposition77

end DomainTheory.NeighbourhoodSystems
