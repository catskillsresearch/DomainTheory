/-ai
For a subsystem, the finitely generated subsystem of a list is contained in the subsystem if and only if every generator named by the list belongs to the subsystem.

Proceed by induction on the list. If the list is empty, there is no generator to check, and any member has empty witnessing sublist, so it equals the master, which belongs to the subsystem because the masters agree. If the list has a head, the generator condition splits into the head and the tail. Containment yields the head, because its principal generator belongs to the finitely generated subsystem, and yields the tail by monotonicity along the tail sublist. Conversely, a member whose witnessing sublist omits the head already lies in the tail subsystem. If the witnessing sublist includes the head, the partial meet is the intersection of the head generator with the tail meet. The tail meet is a neighbourhood because the full meet witnesses it, the inductive inclusion puts the tail meet in the subsystem, and the subsystem is closed under that consistent intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen_mono
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.principal_mem_finGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.interFrom_cons_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **The workhorse lemma.** For any subsystem `D' ◁ D`, `Fin(js) ⊆ D'.mem` iff every single
generator `P.X i` (`i ∈ js`) already lies in `D'.mem`. Proved by induction on `js`: the `cons` step
uses `interFrom_mem_of_witness` (`Theorem75.lean`) to show that the "tail" sub-meet of a consistent
`j :: sub`-selection is itself consistent (using the *full* meet as witness), then combines via
`D'.inter_closed`. -/
theorem finGen_le_iff_forall_mem {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    finGen P js ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  induction js with
  | nil =>
    refine ⟨fun _ i hi => absurd hi List.not_mem_nil, fun _ => ?_⟩
    rintro Y ⟨sub, hsub, _, hYeq⟩
    rw [List.eq_nil_of_sublist_nil hsub] at hYeq
    rw [hYeq, show interFrom P D.master ([] : List ℕ) = D.master from rfl, ← hD'.master_eq]
    exact D'.master_mem
  | cons j js' ih =>
    rw [List.forall_mem_cons]
    constructor
    · intro hsub
      refine ⟨hsub (principal_mem_finGen P List.mem_cons_self), ?_⟩
      exact ih.mp ((finGen_mono P (List.sublist_cons_self j js')).trans hsub)
    · intro hall
      have hj := hall.1
      have hFinjs' : finGen P js' ⊆ D'.mem := ih.mpr hall.2
      rintro Y ⟨sub, hsub, hDY, hYeq⟩
      cases hsub with
      | cons _ hsub' => exact hFinjs' ⟨sub, hsub', hDY, hYeq⟩
      | cons_cons _ hsub' =>
        rename_i sub2
        rw [interFrom_cons_eq P D.master j sub2] at hYeq
        set Y2 := interFrom P D.master sub2 with hY2def
        have hY_sub_Y2 : Y ⊆ Y2 := hYeq ▸ Set.inter_subset_right
        have hDY2 : D.mem Y2 := interFrom_mem_of_witness P hDY hY_sub_Y2 D.master_mem
        have hY2mem : D'.mem Y2 := hFinjs' ⟨sub2, hsub', hDY2, rfl⟩
        have hXYmem : D.mem (P.X j ∩ Y2) := hYeq ▸ hDY
        exact hYeq ▸ hD'.inter_closed hj hY2mem hXYmem

end FinGen

end DomainTheory.NeighbourhoodSystems
