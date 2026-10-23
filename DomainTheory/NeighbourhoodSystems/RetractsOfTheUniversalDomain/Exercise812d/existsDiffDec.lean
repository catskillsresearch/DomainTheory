module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.diff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

/-- **Extracted existence decider for `\`**: `1` iff `∃ k, X k = X n \ X m`
(`IsComputableDiff.diff_computable`'s own predicate). -/
noncomputable def existsDiffDec : ℕ → ℕ := fun t => isOne (hDiff.diff_computable.choose t)

end DirectDec

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsDiffDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem le_one (t : ℕ) : existsDiffDec P hDiff t ≤ 1 := isOne_le_one _

end DirectDec

end existsDiffDec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsDiffDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem spec (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 1 ↔ ∃ k, P.X k = P.X n \ P.X m := by
  unfold existsDiffDec
  rw [isOne_eq_one_iff]
  have h := hDiff.diff_computable.choose_spec.2 (Nat.pair n m)
  dsimp only at h
  rw [unpair_pair_fst, unpair_pair_snd] at h
  exact h.symm

end DirectDec

end existsDiffDec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace existsDiffDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

/-- **The `\`-existence decider matches non-emptiness**, via `IsComputableDiff.diff.exists_iff_ne_empty`. -/
theorem eq_zero_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    existsDiffDec P hDiff (Nat.pair n m) = 0 ↔ P.X n \ P.X m = ∅ := by
  have hle := existsDiffDec.le_one P hDiff (Nat.pair n m)
  have h1 := existsDiffDec.spec P hDiff n m
  have h2 := IsComputableDiff.diff.exists_iff_ne_empty (P := P) hdiff hnomin n m
  constructor
  · intro h0
    by_contra hne
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := h1.mpr (h2.mpr hne)
    omega
  · intro hempty
    by_contra hne0
    have h1' : existsDiffDec P hDiff (Nat.pair n m) = 1 := by omega
    exact (h2.mp (h1.mp h1')) hempty

end DirectDec

end existsDiffDec
end DomainTheory.NeighbourhoodSystems
