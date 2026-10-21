/-ai
Theorem 8.5, from Scott's step-closure formula to a finitary projection, states that if a neighbourhood Y belongs to a of x exactly when Y belongs to E and some neighbourhood of x is contained in Y and related to itself by a, then a is a finitary projection.

The proof shows that a equals the retraction of the subsystem of neighbourhoods that a relates to themselves. Extensionality of approximable maps reduces the equality to the relation. A relation of a, read at the principal of its domain, is rewritten by the formula and reassembled as the retraction relation. A retraction witness is sent back by the same principal reading and by the fact that a self-related neighbourhood of an element, contained in the output, belongs to the image of that element. The retraction of a subsystem is a finitary projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.fixedNbhd_subsystem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.mem_of_exists_rel_self

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}





/-- **Theorem 8.5, `(ii) ⟹ (i)` (Scott 1981, PRG-19).** If `a` satisfies Scott's step-closure
formula `a(x) = {Y ∈ E ∣ ∃X∈x, X⊆Y ∧ XaX}` for every `x ∈ |E|`, then `a` is a finitary projection.

The proof shows `a` literally *is* `retractionOfSubsystem` for `D = fixedNbhd a`: unwinding formula
(ii) at a principal `x = ↑X` via `rel_iff_mem_principal` reproduces exactly
`retractionOfSubsystem_rel`'s formula. Definition 8.3's corollaries of Proposition 8.2 then finish
the proof — no further work needed. -/
theorem isFinitaryProjection_of_formula (a : ApproximableMap E E)
    (hii : ∀ (x : E.Element) {Y : Set α}, (a.toElementMap x).mem Y ↔
      E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y ∧ a.rel X X) :
    IsFinitaryProjection a := by
  have heq : a = Subsystem.retractionOfSubsystem (fixedNbhd_subsystem a) := by
    apply ApproximableMap.ext
    intro X Z
    rw [Subsystem.retractionOfSubsystem_rel]
    constructor
    · intro hr
      have hX : E.mem X := a.rel_dom hr
      have hmem : (a.toElementMap (E.principal hX)).mem Z := (a.rel_iff_mem_principal hX).mp hr
      obtain ⟨hZE, Y, hXY, hYZ, hYa⟩ := hii (E.principal hX) |>.mp hmem
      exact ⟨hX, hZE, Y, ⟨a.rel_dom hYa, hYa⟩, (E.mem_principal hX).mp hXY |>.2, hYZ⟩
    · rintro ⟨hX, hZ, Y, ⟨_, hYa⟩, hXY, hYZ⟩
      exact (a.rel_iff_mem_principal hX).mpr
        (mem_of_exists_rel_self (E.principal hX) hZ (E.mem_principal hX |>.mpr ⟨a.rel_dom hYa, hXY⟩)
          hYZ hYa)
  rw [heq]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem a)

end DomainTheory.NeighbourhoodSystems
