module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_19
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Algebra.Group.End

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def upSet (X : Set α) : Set (Set α) := {Y | V.mem Y ∧ Y ⊆ X}

@[simp] theorem mem_upSet {X Y : Set α} : Y ∈ V.upSet X ↔ V.mem Y ∧ Y ⊆ X := Iff.rfl

theorem upSet_inter (X Y : Set α) : V.upSet X ∩ V.upSet Y = V.upSet (X ∩ Y) := by
  ext Z
  simp only [Set.mem_inter_iff, mem_upSet, Set.subset_inter_iff]
  tauto

theorem upSet_subset_iff {X Y : Set α} (hX : V.mem X) : V.upSet X ⊆ V.upSet Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h ⟨hX, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hZ.2.trans hXY⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def powerSystem : NeighborhoodSystem (Set α) where
  mem S := ∃ X, V.mem X ∧ S = V.upSet X
  master := V.upSet V.master
  master_nonempty := ⟨V.master, V.master_mem, subset_rfl⟩
  master_mem := ⟨V.master, V.master_mem, rfl⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hZin : Z ∈ V.upSet X ∩ V.upSet Y := hWsub ⟨hZ, subset_rfl⟩
    obtain ⟨⟨_, hZX⟩, _, hZY⟩ := hZin
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hZX hZY)
    exact ⟨X ∩ Y, hXY, V.upSet_inter X Y⟩
  sub_master := by
    intro S hS
    obtain ⟨X, hX, rfl⟩ := hS
    exact (V.upSet_subset_iff hX).mpr (V.sub_master hX)

@[simp] theorem powerSystem_mem {S : Set (Set α)} :
    V.powerSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.upSet X := Iff.rfl

def ofPower (y : V.powerSystem.Element) : V.Element where
  mem W := V.mem W ∧ y.mem (V.upSet W)
  sub h := h.1
  master_mem := ⟨V.master_mem, y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.upSet X ∩ V.upSet Y) := y.inter_mem hyX hyY
    rw [V.upSet_inter] at hyInter
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hWin : W ∈ V.upSet (X ∩ Y) := by rw [hWeq]; exact ⟨hW, subset_rfl⟩
    exact ⟨V.inter_mem hX hY hW hWin.2, hyInter⟩
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.upSet_subset_iff hX).mpr hXY)⟩

def toPower (x : V.Element) : V.powerSystem.Element where
  mem S := ∃ W, x.mem W ∧ S = V.upSet W
  sub := by rintro S ⟨W, hW, rfl⟩; exact ⟨W, x.sub hW, rfl⟩
  master_mem := ⟨V.master, x.master_mem, rfl⟩
  inter_mem := by
    rintro S T ⟨W1, hW1, rfl⟩ ⟨W2, hW2, rfl⟩
    exact ⟨W1 ∩ W2, x.inter_mem hW1 hW2, V.upSet_inter W1 W2⟩
  up_mem := by
    rintro S T ⟨W, hW, rfl⟩ hT hsub
    obtain ⟨W', hW', rfl⟩ := hT
    exact ⟨W', x.up_mem hW hW' ((V.upSet_subset_iff (x.sub hW)).mp hsub), rfl⟩

theorem upSet_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.upSet X = V.upSet Y) : X = Y :=
  Set.Subset.antisymm ((V.upSet_subset_iff hX).mp h.subset)
    ((V.upSet_subset_iff hY).mp h.superset)

def powerIso : V.Element ≃o V.powerSystem.Element where
  toFun := V.toPower
  invFun := V.ofPower
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hW, W', hW', heq⟩
      rw [V.upSet_injective hW (x.sub hW') heq]; exact hW'
    · intro hx
      exact ⟨x.sub hx, W, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨W, ⟨_, hyW⟩, rfl⟩
      exact hyW
    · intro hyS
      obtain ⟨W, hW, rfl⟩ := y.sub hyS
      exact ⟨W, ⟨hW, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hx
      have hmem : (V.toPower x).mem (V.upSet W) := ⟨W, hx, rfl⟩
      obtain ⟨W', hW', heq⟩ := h (V.upSet W) hmem
      rw [V.upSet_injective (x.sub hx) (x'.sub hW') heq]; exact hW'
    · intro h S hS
      obtain ⟨W, hW, rfl⟩ := hS
      exact ⟨W, h W hW, rfl⟩

theorem isomorphic_powerSystem : V ≅ᴰ V.powerSystem := ⟨V.powerIso⟩

theorem powerSystem_isPositive : V.powerSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.upSet_inter]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨W, hW, subset_rfl⟩
  · rintro ⟨Z, hZmem, hZsub⟩
    exact ⟨X ∩ Y, V.inter_mem hX hY hZmem hZsub, rfl⟩

theorem toPower_principal {X : Set α} (hX : V.mem X) :
    V.toPower (V.principal hX) = V.powerSystem.principal ⟨X, hX, rfl⟩ := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨W, ⟨hWmem, hXW⟩, rfl⟩
    exact ⟨⟨W, hWmem, rfl⟩, (V.upSet_subset_iff hX).mpr hXW⟩
  · rintro ⟨⟨W, hWmem, rfl⟩, hsub⟩
    exact ⟨W, ⟨hWmem, (V.upSet_subset_iff hX).mp hsub⟩, rfl⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

set_option linter.unusedVariables false

theorem example_120.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)))))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))))))
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_powerSystem
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem_isPositive)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower_principal
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def basicOpen (X : Set α) : Set V.Element := {x | x.mem X}

@[simp] theorem mem_basicOpen {X : Set α} {x : V.Element} :
    x ∈ V.basicOpen X ↔ x.mem X := Iff.rfl

class OpenFilter (U : Set V.Element) : Prop where
  out : ∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U

theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right

instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.OpenFilter
  isOpen_univ := ⟨fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩⟩
  isOpen_inter := by
    intro U W hU hW
    constructor
    intro x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU.out x hxU
    obtain ⟨Y, hY, hYW⟩ := hW.out x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS
    constructor
    intro x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := (hS t htS).out x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
