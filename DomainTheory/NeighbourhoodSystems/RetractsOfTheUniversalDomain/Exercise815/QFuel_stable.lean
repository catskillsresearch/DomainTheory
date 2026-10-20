/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.unpair_snd_lt_of_unpair_fst_pos
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QBody_local
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.QFuel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

section TreeVal

variable (r : ℕ → ℕ)

/-- **Stabilization.** Once the fuel exceeds the code, `QFuel r`'s value no longer depends on
*which* sufficiently-large fuel was supplied — the key fact letting us read off a genuine,
fuel-free evaluator `TreeVal` below. Proved by strong induction on `c`, splitting on whether `c`'s
tag is `0` (no recursion, both sides agree immediately) or positive (both children are strictly
`< c`, via `unpair_snd_lt_of_unpair_fst_pos`, so the induction hypothesis applies to them). -/
theorem QFuel_stable :
    ∀ c fuel fuel', c < fuel → c < fuel' → QFuel r fuel c = QFuel r fuel' c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro fuel fuel' hfuel hfuel'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    show QBody r (QFuel r f) c = QBody r (QFuel r f') c
    rcases Nat.eq_zero_or_pos c.unpair.1 with htag0 | htagpos
    · have hval : isOne (1 - c.unpair.1) = 1 := by rw [htag0]; rfl
      unfold QBody
      simp only [hval, selectFn_one]
    · have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos htagpos
      have h1lt : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
      have h2lt : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
      have hfc : c ≤ f := by omega
      have hfc' : c ≤ f' := by omega
      have e1 := ih c.unpair.2.unpair.1 h1lt f f'
        (lt_of_lt_of_le h1lt hfc) (lt_of_lt_of_le h1lt hfc')
      have e2 := ih c.unpair.2.unpair.2 h2lt f f'
        (lt_of_lt_of_le h2lt hfc) (lt_of_lt_of_le h2lt hfc')
      exact QBody_local r (QFuel r f) (QFuel r f') c e1 e2

end TreeVal

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
