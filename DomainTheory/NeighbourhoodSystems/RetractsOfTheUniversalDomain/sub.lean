module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_11

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)

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

theorem mono {f g : ApproximableMap E E} (h : f ≤ g) : sub f ≤ sub g := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := rel.mp hr
  exact rel.mpr ⟨hX, hZ, Y, ⟨hYE, h Y Y hYf⟩, hXY, hYZ⟩

theorem retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    sub (Subsystem.retractionOfSubsystem h) = Subsystem.retractionOfSubsystem h := by
  unfold sub
  congr 1
  exact fixedNbhd_retractionOfSubsystem h

end sub

def finitaryProjectionSubsystemEquiv (E : NeighborhoodSystem α) :
    {f : ApproximableMap E E // sub f = f} ≃o {D : NeighborhoodSystem α // D ◁ E} where
  toFun f := ⟨fixedNbhd f.1, fixedNbhd_subsystem f.1⟩
  invFun D := ⟨Subsystem.retractionOfSubsystem D.2, sub.retractionOfSubsystem D.2⟩
  left_inv f := Subtype.ext f.2
  right_inv D := Subtype.ext (fixedNbhd_retractionOfSubsystem D.2)
  map_rel_iff' := by
    intro f g
    constructor
    · intro hle
      have hleD : fixedNbhd f.1 ◁ fixedNbhd g.1 := hle
      have hsub : sub f.1 ≤ sub g.1 := by
        rintro X Z hXZ
        rw [sub.rel] at hXZ ⊢
        obtain ⟨hX, hZ, Y, hY, hXY, hYZ⟩ := hXZ
        exact ⟨hX, hZ, Y, hleD.sub hY, hXY, hYZ⟩
      rwa [f.2, g.2] at hsub
    · intro hfg
      show fixedNbhd f.1 ◁ fixedNbhd g.1
      refine (Subsystem.subsystem_iff_subset_of_common
        (fixedNbhd_subsystem f.1) (fixedNbhd_subsystem g.1)).mpr ?_
      intro X hX
      exact ⟨hX.1, hfg X X hX.2⟩

theorem fixedNbhd_sub (f : ApproximableMap E E) : fixedNbhd (sub f) = fixedNbhd f := by
  apply NeighborhoodSystem.ext
  · intro Y
    constructor
    · intro hmem
      have hr : (sub f).rel Y Y := hmem.2
      obtain ⟨hYE, -, Y', hY', hYY', hY'Y⟩ := sub.rel.mp hr
      obtain ⟨hY'E, hY'f⟩ := hY'
      have hYY'eq : Y' = Y := Set.Subset.antisymm hY'Y hYY'
      exact ⟨hYE, hYY'eq ▸ hY'f⟩
    · intro hmem
      obtain ⟨hYE, hYf⟩ := hmem
      refine ⟨hYE, sub.rel.mpr ⟨hYE, hYE, Y, ⟨hYE, hYf⟩, subset_rfl, subset_rfl⟩⟩
  · rfl

theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    FinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)

theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub.rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ

theorem sub_eq_self_of_isFinitaryProjection {f : ApproximableMap E E}
    (h : FinitaryProjection f) : sub f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · exact sub_le f X Z
  · intro hXZ
    have hX : E.mem X := f.rel_dom hXZ
    have hZ : E.mem Z := f.rel_cod hXZ
    have hmem : (f.toElementMap (E.principal hX)).mem Z := (f.rel_iff_mem_principal hX).mp hXZ
    obtain ⟨-, W, hW, hWZ, hWf⟩ := (formula_of_isFinitaryProjection h (E.principal hX)).mp hmem
    obtain ⟨hWE, hXW⟩ := (E.mem_principal hX).mp hW
    exact sub.rel.mpr ⟨hX, hZ, W, ⟨hWE, hWf⟩, hXW, hWZ⟩

theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ FinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩

theorem sub_sub (f : ApproximableMap E E) : sub (sub f) = sub f := by
  unfold sub
  congr 1
  exact fixedNbhd_sub f

theorem isFinitaryProjection_sub (f : ApproximableMap E E) : FinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)

end DomainTheory.NeighbourhoodSystems
