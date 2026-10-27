module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/- concordance: source L4890 THEOREM 8.6 sub combinator -/
/-- **Theorem 8.6's combinator `sub(f)` (Scott 1981, PRG-19), per token `f`.** Scott's formula
`X sub(f) Z ↔ ∃Y ∈ E, X⊆Y ∧ f.rel Y Y ∧ Y⊆Z` is literally `retractionOfSubsystem` applied to
`fixedNbhd f = {Y ∈ E ∣ Y f Y}` (Theorem 8.5's subsystem, built for *any* `f`). -/
def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)

/-- `fixedNbhd (retractionOfSubsystem h) = D`: the round trip recovering a subsystem `D` from the
retraction it induces. `Y (retractionOfSubsystem h) Y ↔ ∃W∈D, Y⊆W⊆Y`, and `Y⊆W⊆Y` forces `W=Y`, so
this says exactly `D.mem Y` (using `E.mem Y` for free from `D ⊆ E`). -/
theorem fixedNbhd_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    fixedNbhd (Subsystem.retractionOfSubsystem h) = D := by
  apply NeighborhoodSystem.ext
  · intro X
    rw [fixedNbhd_mem, Subsystem.retractionOfSubsystem_rel]
    constructor
    · rintro ⟨hXE, -, -, Y, hY, hXY, hYX⟩
      rw [Set.Subset.antisymm hXY hYX]
      exact hY
    · intro hX
      exact ⟨h.sub hX, h.sub hX, h.sub hX, X, hX, subset_rfl, subset_rfl⟩
  · exact h.master_eq.symm

namespace sub

@[simp] theorem rel {f : ApproximableMap E E} {X Z : Set α} :
    (sub f).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, (E.mem Y ∧ f.rel Y Y) ∧ X ⊆ Y ∧ Y ⊆ Z :=
  Subsystem.retractionOfSubsystem_rel (fixedNbhd_subsystem f)

/-- **`sub` is monotone.** `f ≤ g → sub f ≤ sub g`: immediate from `fixedNbhd`'s definition, since
`f.rel Y Y → g.rel Y Y` whenever `f ≤ g`. -/
theorem mono {f g : ApproximableMap E E} (h : f ≤ g) : sub f ≤ sub g := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := rel.mp hr
  exact rel.mpr ⟨hX, hZ, Y, ⟨hYE, h Y Y hYf⟩, hXY, hYZ⟩

/-- Every `retractionOfSubsystem h` is already a fixed point of `sub` — immediate from the round
trip `fixedNbhd_retractionOfSubsystem`, since `sub` is *defined* as `retractionOfSubsystem` applied
to `fixedNbhd`. -/
theorem retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    sub (Subsystem.retractionOfSubsystem h) = Subsystem.retractionOfSubsystem h := by
  unfold sub
  congr 1
  exact fixedNbhd_retractionOfSubsystem h

end sub

end DomainTheory.NeighbourhoodSystems
