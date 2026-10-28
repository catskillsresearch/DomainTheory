module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_27
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import Mathlib.Algebra.Group.End

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def tokenSystem : NeighborhoodSystem V.Element where
  mem S := ∃ X, V.mem X ∧ S = V.bracket X
  master := Set.univ
  master_nonempty := ⟨V.bot, Set.mem_univ _⟩
  master_mem := ⟨V.master, V.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hpz := hWsub (V.principal_mem_bracket hZ)
    obtain ⟨hzX, hzY⟩ := hpz
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hzX.2 hzY.2)
    exact ⟨X ∩ Y, hXY, V.bracket_inter hX hY⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem tokenSystem_mem {S : Set V.Element} :
    V.tokenSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.bracket X := Iff.rfl

def ofToken (y : V.tokenSystem.Element) : V.Element where
  mem X := V.mem X ∧ y.mem (V.bracket X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [V.bracket_master]; exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.bracket X ∩ V.bracket Y) := y.inter_mem hyX hyY
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hpw := V.principal_mem_bracket hW
    rw [← hWeq] at hpw
    obtain ⟨hwX, hwY⟩ := hpw
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hW (Set.subset_inter hwX.2 hwY.2)
    refine ⟨hXY, ?_⟩
    rw [← V.bracket_inter hX hY]
    exact hyInter
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.bracket_subset_iff hX hY).mpr hXY)⟩

def toToken (x : V.Element) : V.tokenSystem.Element where
  mem S := ∃ X, x.mem X ∧ S = V.bracket X
  sub := by rintro S ⟨X, hX, rfl⟩; exact ⟨X, x.sub hX, rfl⟩
  master_mem := ⟨V.master, x.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    exact ⟨X ∩ Y, x.inter_mem hX hY, V.bracket_inter (x.sub hX) (x.sub hY)⟩
  up_mem := by
    rintro S T ⟨X, hX, rfl⟩ hT hsub
    obtain ⟨Y, hYmem, rfl⟩ := hT
    exact ⟨Y, x.up_mem hX hYmem ((V.bracket_subset_iff (x.sub hX) hYmem).mp hsub), rfl⟩

def tokenIso : V.Element ≃o V.tokenSystem.Element where
  toFun := V.toToken
  invFun := V.ofToken
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨hX, X', hX', heq⟩
      rw [V.bracket_injective hX (x.sub hX') heq]; exact hX'
    · intro hx
      exact ⟨x.sub hx, X, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨X, ⟨_, hyX⟩, rfl⟩
      exact hyX
    · intro hyS
      obtain ⟨X, hX, rfl⟩ := y.sub hyS
      exact ⟨X, ⟨hX, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hx
      have hmem : (V.toToken x).mem (V.bracket X) := ⟨X, hx, rfl⟩
      obtain ⟨X', hX', heq⟩ := h (V.bracket X) hmem
      rw [V.bracket_injective (x.sub hx) (x'.sub hX') heq]; exact hX'
    · intro h S hS
      obtain ⟨X, hX, rfl⟩ := hS
      exact ⟨X, h X hX, rfl⟩

theorem bracket_inter_nonempty_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    (V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  constructor
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨X ∩ Y, x.sub (x.inter_mem hxX hxY), subset_rfl⟩
  · rintro ⟨Z, hZ, hZsub⟩
    refine ⟨V.principal hZ, ?_, ?_⟩
    · exact ⟨hX, hZsub.trans Set.inter_subset_left⟩
    · exact ⟨hY, hZsub.trans Set.inter_subset_right⟩

theorem isomorphic_tokenSystem : V ≅ᴰ V.tokenSystem := ⟨V.tokenIso⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
section

set_option linter.unusedVariables false

theorem theorem_110.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX)) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y)))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter_nonempty_iff
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_tokenSystem)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal_mem_bracket
end

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

def filterFixedBy (x : V.Element) : V.tokenSystem.Element := V.toToken x

theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩
end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
