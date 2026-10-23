module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- **Extracted existence decider for `∩`**: `1` iff `∃ k, X k ⊆ X n ∩ X m` (`cons_computable`'s
own predicate). -/
noncomputable def existsInterDec : ℕ → ℕ := fun t => isOne (P.cons_computable.choose t)

end DirectDec

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsInterDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

theorem le_one (t : ℕ) : existsInterDec P t ≤ 1 := isOne_le_one _

end DirectDec

end existsInterDec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsInterDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

theorem spec (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
  unfold existsInterDec
  rw [isOne_eq_one_iff]
  have h := P.cons_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

end DirectDec

end existsInterDec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsInterDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- **The `∩`-existence decider matches non-emptiness**, given `IsPositive` + `NoMinimal`: any
consistency witness is itself a non-empty neighbourhood (`NoMinimal.mem_ne_empty`), and conversely
a non-empty intersection is a neighbourhood by `IsPositive`, hence indexed by `surj`. -/
theorem eq_zero_iff (hpos : V.IsPositive) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsInterDec P (Nat.pair n m) = 0 ↔ P.X n ∩ P.X m = ∅ := by
  have hle := existsInterDec.le_one P (Nat.pair n m)
  constructor
  · intro h0
    by_contra hne
    have hmem : V.mem (P.X n ∩ P.X m) :=
      (hpos (P.mem_X n) (P.mem_X m)).mpr (Set.nonempty_iff_ne_empty.mpr hne)
    obtain ⟨k, hk⟩ := P.surj hmem
    have h1 : existsInterDec P (Nat.pair n m) = 1 :=
      (existsInterDec.spec P n m).mpr ⟨k, by rw [hk]⟩
    omega
  · intro hempty
    by_contra hne1
    have h1 : existsInterDec P (Nat.pair n m) = 1 := by omega
    obtain ⟨k, hk⟩ := (existsInterDec.spec P n m).mp h1
    exact absurd (Set.subset_eq_empty hk hempty) (hnomin.mem_ne_empty (P.mem_X k))

end DirectDec

end existsInterDec
end DomainTheory.NeighbourhoodSystems
