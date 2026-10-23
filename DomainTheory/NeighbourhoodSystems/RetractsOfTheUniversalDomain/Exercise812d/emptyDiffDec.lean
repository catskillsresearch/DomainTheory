module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.existsDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.union

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

/-- **The `\`-emptiness decider** (`1` iff `X n \ X m = ∅`). -/
noncomputable def emptyDiffDec : ℕ → ℕ := fun t => 1 - existsDiffDec P hDiff t

end DirectDec

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace emptyDiffDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem le_one (t : ℕ) : emptyDiffDec P hDiff t ≤ 1 := by
  unfold emptyDiffDec; have := existsDiffDec.le_one P hDiff t; omega

end DirectDec

end emptyDiffDec
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace emptyDiffDec

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

section DirectDec

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable (hDiff : IsComputableDiff P)

theorem eq_one_iff (hdiff : V.DiffClosed) (hnomin : V.NoMinimal) (n m : ℕ) :
    emptyDiffDec P hDiff (Nat.pair n m) = 1 ↔ P.X n \ P.X m = ∅ := by
  unfold emptyDiffDec
  have hle := existsDiffDec.le_one P hDiff (Nat.pair n m)
  have h0 := existsDiffDec.eq_zero_iff P hDiff hdiff hnomin n m
  constructor
  · intro h1; apply h0.mp; omega
  · intro hempty; have := h0.mpr hempty; omega

end DirectDec

end emptyDiffDec
end DomainTheory.NeighbourhoodSystems
